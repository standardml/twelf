(* Meta Theorem Prover abstraction : Version 1.3 *)
(* Author: Frank Pfenning, Carsten Schuermann *)

functor MTPAbstract (structure IntSyn' : INTSYN
		     structure StateSyn' : STATESYN
		     structure Whnf    : WHNF
		       sharing Whnf.IntSyn = IntSyn'
		     structure Constraints : CONSTRAINTS
		       sharing Constraints.IntSyn = IntSyn'
		     structure Subordinate : SUBORDINATE
		       sharing Subordinate.IntSyn = IntSyn'
		     structure Trail : TRAIL
		       sharing Trail.IntSyn = IntSyn')
  : MTPABSTRACT =
struct

  structure IntSyn = IntSyn'
  structure StateSyn = StateSyn'
    
  exception Error of string
    
  local

    structure I = IntSyn
    structure S = StateSyn
    structure C = Constraints
      
    (* Intermediate Data Structure *)

    datatype EFVar =
      EV of I.Exp option ref * I.Exp * S.Tag
					(* y ::= (X , {G} V)  if G |- X : V *)
    | FV of I.name * I.Exp		(*     | (F , {G} V)  if G |- F : V *)

    (*
       We write {{K}} for the context of K, where EVars and FVars have
       been translated to declarations and their occurrences to BVars.
       We write {{U}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts G, any K is implicitly assumed to be
       well-formed and in dependency order.

       We write  K ||- U  if all EVars and FVars in U are collected in K.
       In particular, . ||- U means U contains no EVars or FVars.  Similarly,
       for spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)

    (* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)
    fun checkEmpty (nil) = ()
      | checkEmpty (Cnstr) =
        (case C.simplify Cnstr
	   of nil => ()
	    | _ => raise Error "Typing ambiguous -- unresolved constraints")

    (* eqEVar X Y = B
       where B iff X and Y represent same variable
    *)
    fun eqEVar (I.EVar (r1, _, _, _)) (EV (r2,  _, _)) = (r1 = r2)
      | eqEVar _ _ = false

    (* eqFVar F Y = B
       where B iff X and Y represent same variable
    *)
    fun eqFVar (I.FVar (n1, _, _)) (FV (n2,  _)) = (n1 = n2)
      | eqFVar _ _ = false

    (* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)
    fun exists P K =
        let fun exists' (I.Null) = false
	      | exists' (I.Decl(K',Y)) = P(Y) orelse exists' (K')
	in
	  exists' K
	end


    fun or (I.Maybe, _) = I.Maybe
      | or (_, I.Maybe) = I.Maybe
      | or (I.Virtual, _) = I.Virtual
      | or (_, I.Virtual) = I.Virtual
      | or (I.No, I.No) = I.No

      
    (* occursInExp (k, U) = DP, 

       Invariant:
       If    U in nf 
       then  DP = No      iff k does not occur in U
	     DP = Maybe   iff k occurs in U some place not as an argument to a Skonst
	     DP = Virtual iff k occurs in U and only as arguments to Skonsts
    *)
    fun occursInExp (k, I.Uni _) = I.No
      | occursInExp (k, I.Pi (DP, V)) = or (occursInDecP (k, DP), occursInExp (k+1, V))
      | occursInExp (k, I.Root (H, S)) = occursInHead (k, H, occursInSpine (k, S))
      | occursInExp (k, I.Lam (D, V)) = or (occursInDec (k, D), occursInExp (k+1, V))
      (* no case for Redex, EVar, EClo *)

    and occursInHead (k, I.BVar (k'), DP) = 
        if (k = k') then I.Maybe
	else DP
      | occursInHead (k, I.Const _, DP) = DP
      | occursInHead (k, I.Def _, DP) = DP
      | occursInHead (k, I.Skonst _, I.No) = I.No
      | occursInHead (k, I.Skonst _, I.Virtual) = I.Virtual
      | occursInHead (k, I.Skonst _, I.Maybe) = I.Virtual
      (* no case for FVar *)

    and occursInSpine (_, I.Nil) = I.No
      | occursInSpine (k, I.App (U, S)) = or (occursInExp (k, U), occursInSpine (k, S))
      (* no case for SClo *)

    and occursInDec (k, I.Dec (_, V)) = occursInExp (k, V)
    and occursInDecP (k, (D, _)) = occursInDec (k, D)

    (* piDepend ((D,P), V) = Pi ((D,P'), V)
       where P' = Maybe if D occurs in V, P' = No otherwise 
    *)
    (* optimize to have fewer traversals? -cs *)
    (* pre-Twelf 1.2 code walk Fri May  8 11:17:10 1998 *)
    fun piDepend (DPV as ((D, I.No), V)) = I.Pi DPV
      | piDepend (DPV as ((D, I.Virtual), V)) = I.Pi DPV
      | piDepend ((D, I.Maybe), V) = 
	  I.Pi ((D, occursInExp (1, V)), V)
	
    (* weaken (depth,  G, a) = (w')
    *)
    fun weaken (I.Null, a) = I.id 
      | weaken (I.Decl (G', D as I.Dec (name, V)), a) = 
        let 
	  val w' = weaken (G', a)
	in
	  if Subordinate.belowEq (I.targetFam V, a) then I.dot1 w'
	  else I.comp (w', I.shift)
	end

    (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
    fun raiseType (I.Null, V) = V
      | raiseType (I.Decl (G, D), V) = raiseType (G, I.Pi ((D, I.Maybe), V))

    (* collectExpW (G, (U, s), K) = K'

       Invariant: 
       If    G |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
             (enforced by extended occurs-check for FVars in Unify)
       and   K' = K, K''
	     where K'' contains all EVars and FVars in (U,s)
    *)
    (* Possible optimization: Calculate also the normal form of the term *)
    fun collectExpW (T, G, (I.Uni L, s), K) = K
      | collectExpW (T, G, (I.Pi ((D, _), V), s), K) =
          collectExp (T, I.Decl (G, I.decSub (D, s)), (V, I.dot1 s), collectDec (T, G, (D, s), K))
      | collectExpW (T, G, (I.Root (F as I.FVar (name, V, s'), S), s), K) =
	if exists (eqFVar F) K
	  then collectSpine (T, G, (S, s), K)
	else (* s' = ^|G| *)
	  collectSpine (T, G, (S, s), I.Decl (collectExp (T, I.Null, (V, I.id), K), FV (name, V)))
      | collectExpW (T, G, (I.Root (_ , S), s), K) =
	  collectSpine (S.decrease T, G, (S, s), K)
      | collectExpW (T, G, (I.Lam (D, U), s), K) =
	  collectExp (T, I.Decl (G, I.decSub (D, s)), (U, I.dot1 s), collectDec (T, G, (D, s), K))
      | collectExpW (T, G, (X as I.EVar (r, GX, V, Cnstr), s), K) =
	  if exists (eqEVar X) K
	    then collectSub (T, G, s, K)
	  else let
	         val _ = checkEmpty Cnstr
		 val w = weaken (GX, I.targetFam V)
		 val iw = Whnf.invert w
		 val GX' = Whnf.strengthen (iw, GX)
		 val V' = raiseType (GX', I.EClo (V, iw))
		 val X' as I.EVar (r', _, _, _) = I.newEVar (GX', I.EClo (V, iw))
		 val _ = Trail.instantiateEVar (r, I.EClo (X', w))
	       in
		 collectSub (T, G, s, I.Decl (collectExp (T, I.Null, (V', I.id), K), EV(r', V', T)))
	       end
      (* No other cases can occur due to whnf invariant *)

    (* collectExp (T, G, (U, s), K) = K' 
       
       same as collectExpW  but  (U,s) need not to be in whnf 
    *) 
    and collectExp (T, G, Us, K) = collectExpW (T, G, Whnf.whnf Us, K)

    (* collectSpine (T, G, (S, s), K) = K' 

       Invariant: 
       If    G |- s : G1     G1 |- S : V > P
       then  K' = K, K''
       where K'' contains all EVars and FVars in (S, s)
     *)
    and collectSpine (T, G, (I.Nil, _), K) = K
      | collectSpine (T, G, (I.SClo(S, s'), s), K) = 
          collectSpine (T, G, (S, I.comp (s', s)), K)
      | collectSpine (T, G, (I.App (U, S), s), K) =
	  collectSpine (T, G, (S, s), collectExp (T, G, (U, s), K))

    (* collectDec (T, G, (x:V, s), K) = K'

       Invariant: 
       If    G |- s : G1     G1 |- V : L
       then  K' = K, K''
       where K'' contains all EVars and FVars in (V, s)
    *)
    and collectDec (T, G, (I.Dec (_, V), s), K) =
          collectExp (T, G, (V, s), K)

    (* collectSub (T, G, s, K) = K' 

       Invariant: 
       If    G |- s : G1    
       then  K' = K, K''
       where K'' contains all EVars and FVars in s
    *)
    and collectSub (T, G, I.Shift _, K) = K
      | collectSub (T, G, I.Dot (I.Idx _, s), K) = collectSub (T, G, s, K)
      | collectSub (T, G, I.Dot (I.Exp (U), s), K) =
	  collectSub (T, G, s, collectExp (T, G, (U, I.id), K))

    (* abstractEVar (K, depth, X) = C'
     
       Invariant:
       If   G |- X : V
       and  |G| = depth
       and  X occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
    fun abstractEVar (I.Decl (K', EV (r', _, _)), depth, X as I.EVar (r, _, _, _)) =
        if r = r' then I.BVar (depth+1)
	else abstractEVar (K', depth+1, X)
      | abstractEVar (I.Decl (K', FV (n', _)), depth, X) = 
	  abstractEVar (K', depth+1, X)

    (* abstractFVar (K, depth, F) = C'
     
       Invariant:
       If   G |- F : V
       and  |G| = depth
       and  F occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
    fun abstractFVar (I.Decl(K', EV _), depth, F) =
  	  abstractFVar (K', depth+1, F)
      | abstractFVar (I.Decl(K', FV (n', _)), depth, F as I.FVar (n, _, _)) = 
	  if n = n' then I.BVar (depth+1)
	  else abstractFVar (K', depth+1, F)
 
    (* abstractExpW (K, depth, (U, s)) = U'
       U' = {{U[s]}}_K

       Invariant:
       If    G |- s : G1     G1 |- U : V    (U,s) is in whnf
       and   K is internal context in dependency order
       and   |G| = depth
       and   K ||- U and K ||- V
       then  {{K}}, G |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf 
    *)
    fun abstractExpW (K, depth, (U as I.Uni (L), s)) = U
      | abstractExpW (K, depth, (I.Pi ((D, P), V), s)) =
          piDepend ((abstractDec (K, depth, (D, s)), P), 
		    abstractExp (K, depth + 1, (V, I.dot1 s)))
      | abstractExpW (K, depth, (I.Root (F as I.FVar _, S), s)) =
	  I.Root (abstractFVar (K, depth, F), 
		  abstractSpine (K, depth, (S, s)))
      | abstractExpW (K, depth, (I.Root (H, S) ,s)) =
	  I.Root (H, abstractSpine (K, depth, (S, s)))   
      | abstractExpW (K, depth, (I.Lam (D, U), s)) =
          I.Lam (abstractDec (K, depth, (D, s)),
		 abstractExp (K, depth + 1, (U, I.dot1 s)))
      | abstractExpW (K, depth, (X as I.EVar _, s)) =
 	  I.Root (abstractEVar (K, depth, X), 
		  abstractSub (K, depth, s, I.Nil))

    (* abstractExp (K, depth, (U, s)) = U'
     
       same as abstractExpW, but (U,s) need not to be in whnf 
    *)
    and abstractExp (K, depth, Us) = abstractExpW (K, depth, Whnf.whnf Us)

    (* abstractSub (K, depth, s, S) = S'      (implicit raising)
       S' = {{s}}_K @@ S

       Invariant:
       If   G |- s : G1   
       and  |G| = depth
       and  K ||- s
       then {{K}}, G |- S' : {G1}.W > W   (for some W)
       and  . ||- S'
    *)
    and abstractSub (K, depth, I.Shift (k), S) = 
	if k < depth
	  then abstractSub (K, depth, I.Dot (I.Idx (k+1), I.Shift (k+1)), S)
	else (* k = depth *) S
      | abstractSub (K, depth, I.Dot (I.Idx (k), s), S) =
	  abstractSub (K, depth, s, I.App (I.Root (I.BVar (k), I.Nil), S))
      | abstractSub (K, depth, I.Dot (I.Exp (U), s), S) =
	  abstractSub (K, depth, s, I.App (abstractExp (K, depth, (U, I.id)), S))
 
    (* abstractSpine (K, depth, (S, s)) = S'
       where S' = {{S[s]}}_K

       Invariant:
       If   G |- s : G1     G1 |- S : V > P 
       and  K ||- S
       and  |G| = depth

       then {{K}}, G |- S' : V' > P'
       and  . ||- S'
    *)
    and abstractSpine (K, depth, (I.Nil, _))  = I.Nil 
      | abstractSpine (K, depth, (I.SClo (S, s'), s)) = 
	  abstractSpine (K, depth, (S, I.comp (s', s)))
      | abstractSpine (K, depth, (I.App (U, S), s)) =
	  I.App (abstractExp (K, depth, (U ,s)), 
		 abstractSpine (K, depth, (S, s)))

    (* abstractDec (K, depth, (x:V, s)) = x:V'
       where V = {{V[s]}}_K

       Invariant:
       If   G |- s : G1     G1 |- V : L
       and  K ||- V
       and  |G| = depth

       then {{K}}, G |- V' : L
       and  . ||- V'
    *)
    and abstractDec (K, depth, (I.Dec (x, V), s)) =
	  I.Dec (x, abstractExp (K, depth, (V, s)))

    (* getlevel (V) = L if G |- V : L

       Invariant: G |- V : L' for some L'
    *)
    fun getLevel (I.Uni _) = I.Kind 
      | getLevel (I.Pi (_, U)) = getLevel U
      | getLevel (I.Root _)  = I.Type
      | getLevel (I.Redex (U, _)) = getLevel U
      | getLevel (I.Lam (_, U)) = getLevel U
      | getLevel (I.EClo (U,_)) = getLevel U

    (* checkType (V) = () if G |- V : type

       Invariant: G |- V : L' for some L'
    *)
    fun checkType V = 
        (case getLevel V
	   of I.Type => ()
	    | _ => raise Error "Typing ambiguous -- free type variable")

    (* abstractCtx (K, V) = V'
       where V' = {{K}} V

       Invariant: 
       If   {{K}} |- V : L 
       and  . ||- V

       then V' = {{K}} V
       and  . |- V' : L
       and  . ||- V'
    *)
    fun abstractCtx (I.Null) = (I.Null, I.Null)
      | abstractCtx (I.Decl (K', EV (_, V', T))) =
        let
	  val V'' = abstractExp (K', 0, (V', I.id))
	  val _ = checkType V''
	  val (G', B') = abstractCtx K'
	in
	  (I.Decl (G', I.Dec (NONE, V'')), I.Decl (B', T))
	end
(*      | abstractCtx (I.Decl(K', FV (name,V'))) =
	let
	  val V'' = abstractExp (K', 0, (V', I.id))
	  val _ = checkType V''
	  val (G', B') = abstractCtx K'
	in
	  I.Decl (G', I.Dec(SOME(name), V'')),
	  I.Decl (B', S.Assumption n, v
	end *)


    (* abstractSub

       Invariant: 
    *)
    fun abstractSubAll (s, B) =
        let
	  fun abstractSubAll' (K, s' as (I.Shift _)) = s'
	    | abstractSubAll' (K, I.Dot (F as I.Idx _, s')) =
	        I.Dot (F, abstractSubAll' (K, s'))
	    | abstractSubAll' (K, I.Dot (I.Exp U, s')) =
		I.Dot (I.Exp (abstractExp (K, 0, (U, I.id))), abstractSubAll' (K, s'))

	  fun collectSub' ((I.Shift _, _), K) = K
	    | collectSub' ((I.Dot (I.Idx _, s), I.Decl (B, T)), K) = collectSub' ((s, B), K)
	    | collectSub' ((I.Dot (I.Exp (U), s), I.Decl (B, T)), K) =
  	        collectSub' ((s, B), collectExp (T, I.Null, (U, I.id), K))

	  val K = collectSub' ((s, B), I.Null) 
	in
	  (abstractCtx K, abstractSubAll' (K, s))
	end 


  in
    val weaken = weaken
    val raiseType = raiseType

    val abstractSub = abstractSubAll
  end

end;  (* functor MTPAbstract *)
