(* Abstraction (for tabling) *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga, Brigitte Pientka *)

functor AbstractTabled (structure IntSyn' : INTSYN
		  structure Whnf    : WHNF
		    sharing Whnf.IntSyn = IntSyn'
		  structure Unify   : UNIFY
		    sharing Unify.IntSyn = IntSyn'
		  structure Constraints : CONSTRAINTS
		    sharing Constraints.IntSyn = IntSyn'
		  structure Subordinate : SUBORDINATE
		    sharing Subordinate.IntSyn = IntSyn'
		  structure Print : PRINT 
		    sharing Print.IntSyn = IntSyn'
		      )
  : ABSTRACTTABLED =
struct

  structure IntSyn = IntSyn'
    
  exception Error of string

  (* apply strenghening during abstraction *)
  val strengthen = ref false;



    
  local

    structure I = IntSyn
    structure C = Constraints


    datatype EFVar =
      EV of I.Exp			(* Y ::= X         for  GX |- X : VX *)
    | FV of string * I.Exp		(*     | (F , V)      if . |- F : V *)


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


    fun concat (I.Null, G') = G'
      | concat (I.Decl(G, D), G') = I.Decl(concat(G,G'), D)


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


    (* collectConstraints K = cnstrs
       where cnstrs collects all constraints attached to EVars in K
    *)
    fun collectConstraints (I.Null) = nil
      | collectConstraints (I.Decl (G, FV _)) = collectConstraints G
      | collectConstraints (I.Decl (G, EV (I.EVar (_, _, _, ref nil)))) = collectConstraints G
      | collectConstraints (I.Decl (G, EV (I.EVar (_, _, _, ref cnstrL)))) =
        (C.simplify cnstrL) @ collectConstraints G

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
    fun eqEVar (I.EVar (r1, _, _, _)) (EV (I.EVar (r2, _, _, _))) = (r1 = r2)
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
      | or (I.Meta, _) = I.Meta
      | or (_, I.Meta) = I.Meta
      | or (I.No, I.No) = I.No

      
    (* occursInExp (k, U) = DP, 

       Invariant:
       If    U in nf 
       then  DP = No      iff k does not occur in U
	     DP = Maybe   iff k occurs in U some place not as an argument to a Skonst
	     DP = Meta    iff k occurs in U and only as arguments to Skonsts
    *)
    fun occursInExp (k, I.Uni _) = I.No
      | occursInExp (k, I.Pi (DP, V)) = or (occursInDecP (k, DP), occursInExp (k+1, V))
      | occursInExp (k, I.Root (H, S)) = occursInHead (k, H, occursInSpine (k, S))
      | occursInExp (k, I.Lam (D, V)) = or (occursInDec (k, D), occursInExp (k+1, V))
      | occursInExp (k, I.FgnExp (cs, ops)) = occursInExp (k, Whnf.normalize (#toInternal(ops) (), I.id))
      (* no case for Redex, EVar, EClo *)

    and occursInHead (k, I.BVar (k'), DP) = 
        if (k = k') then I.Maybe
	else DP
      | occursInHead (k, I.Const _, DP) = DP
      | occursInHead (k, I.Def _, DP) = DP
      | occursInHead (k, I.FgnConst _, DP) = DP
      | occursInHead (k, I.Skonst _, I.No) = I.No
      | occursInHead (k, I.Skonst _, I.Meta) = I.Meta
      | occursInHead (k, I.Skonst _, I.Maybe) = I.Meta
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
      | piDepend (DPV as ((D, I.Meta), V)) = I.Pi DPV
      | piDepend ((D, I.Maybe), V) = 
	  I.Pi ((D, occursInExp (1, V)), V)
	
    (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
    fun raiseType (I.Null, V) = V
      | raiseType (I.Decl (G, D), V) = raiseType (G, I.Pi ((D, I.Maybe), V))


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

    (* collectExpW (G, (U, s), K) = K'

       Invariant: 
       If    G |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
             (enforced by extended occurs-check for FVars in Unify)
       and   K' = K, K''
	     where K'' contains all EVars and FVars in (U,s)
    *)
    (* Possible optimization: Calculate also the normal form of the term *)
    fun collectExpW (G, (I.Uni L, s), K) = K
      | collectExpW (G, (I.Pi ((D, _), V), s), K) =
          collectExp (I.Decl (G, I.decSub (D, s)), (V, I.dot1 s), collectDec (G, (D, s), K))
      | collectExpW (G, (I.Root (F as I.FVar (name, V, s'), S), s), K) =
	if exists (eqFVar F) K
	  then collectSpine (G, (S, s), K)
	else (* s' = ^|G| *)
	  collectSpine (G, (S, s), I.Decl (collectExp (I.Null, (V, I.id), K), FV (name, V)))
      | collectExpW (G, (I.Root (_ , S), s), K) =
	  collectSpine (G, (S, s), K)
      | collectExpW (G, (I.Lam (D, U), s), K) =
	  collectExp (I.Decl (G, I.decSub (D, s)), (U, I.dot1 s), collectDec (G, (D, s), K))
      | collectExpW (G, (X as I.EVar (r, GX, V, cnstrs), s), K) =
	  if exists (eqEVar X) K
	    then collectSub(G, s, K)
	  else 
	    if (!strengthen) then 
	      let
		(* val _ = checkEmpty !cnstrs *)
		val w = weaken (GX, I.targetFam V)
		val iw = Whnf.invert w 
		val GX' = Whnf.strengthen (iw, GX)
		val X' as I.EVar (r', _, _, _) = I.newEVar (GX', I.EClo (V, iw))
		val _ = Unify.instantiateEVar (r, I.EClo (X', w), nil) 
		val V' = raiseType (GX', I.EClo (V, iw))		 
	      in		
		collectSub(G, I.comp(w, s), I.Decl (collectExp (I.Null, (V', I.id), K), EV (X')))  
	      end
	    else 
	      let
		(* val _ = checkEmpty !cnstrs *)
		val V' = raiseType (GX, V) (* inefficient! *)
	      in
		collectSub(G, s, I.Decl (collectExp (I.Null, (V', I.id), K), EV (X)))
	      end
	      
      | collectExpW (G, (I.FgnExp (cs, ops), s), K) =
          collectExp (G, (#toInternal(ops) (), s), K)
      (* No other cases can occur due to whnf invariant *)

    (* collectExp (G, (U, s), K) = K' 
       
       same as collectExpW  but  (U,s) need not to be in whnf 
    *) 
    and collectExp (G, Us, K) = collectExpW (G, Whnf.whnf Us, K)

    (* collectSpine (G, (S, s), K) = K' 

       Invariant: 
       If    G |- s : G1     G1 |- S : V > P
       then  K' = K, K''
       where K'' contains all EVars and FVars in (S, s)
     *)
    and collectSpine (G, (I.Nil, _), K) = K
      | collectSpine (G, (I.SClo(S, s'), s), K) = 
          collectSpine (G, (S, I.comp (s', s)), K)
      | collectSpine (G, (I.App (U, S), s), K) =
	  collectSpine (G, (S, s), collectExp (G, (U, s), K))

    (* collectDec (G, (x:V, s), K) = K'

       Invariant: 
       If    G |- s : G1     G1 |- V : L
       then  K' = K, K''
       where K'' contains all EVars and FVars in (V, s)
    *)
    and collectDec (G, (I.Dec (_, V), s), K) =
          collectExp (G, (V, s), K)
	  

    (* collectSub (G, s, K) = K' 

       Invariant: 
       If    G |- s : G1    
       then  K' = K, K''
       where K'' contains all EVars and FVars in s
    *)
    and collectSub (G, I.Shift _, K) = K
      | collectSub (G, I.Dot (I.Idx _, s), K) = collectSub (G, s, K)
      | collectSub (G, I.Dot (I.Exp (U), s), K) =      
	  collectSub (G, s, collectExp (G, (U, I.id), K))
    | collectSub (G, I.Dot(Undef, s), K) = collectSub(G, s, K) (* bp Fri Sep 28 17:55:00 2001 ? *)  

    and collectSub' (G, I.Shift _, K) = K
      | collectSub' (G, I.Dot (I.Idx _, s), K) = collectSub' (G, s, K)
      | collectSub' (G, I.Dot (I.Exp (U), s), K) =
        let	  
	  val K' = collectExp (G, (U, I.id), K)
	in 
	  collectSub' (G, s, K')
	end 
      | collectSub'(G, I.Dot(Undef, s), K) = collectSub(G, s, K) (* bp Fri Sep 28 17:55:00 2001 ? *) 

    (* collectCtx (G0, G, K) = (G0', K')
       Invariant:
       If G0 |- G ctx,
       then G0' = G0,G
       and K' = K, K'' where K'' contains all EVars and FVars in G
    *)
    fun collectCtx (G0, I.Null, K) = (G0, K)
      | collectCtx (G0, I.Decl (G, D), K) =
        let
	  val (G0', K') = collectCtx (G0, G, K)
	  val K'' = collectDec (G0', (D, I.id), K')
	in
	  (I.Decl (G0, D), K'')
	end



    (* abstractEVar (K, depth, X) = C'
     
       Invariant:
       If   G |- X : V
       and  |G| = depth
       and  X occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
    fun abstractEVar (I.Decl (K', EV (I.EVar(r',_,_,_))), depth, X as I.EVar (r, _, _, _)) =
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
      | abstractExpW (K, depth, (I.FgnExp (cs, ops), s)) =
          #map(ops) (fn U => abstractExp (K, depth, (U, s)))

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
      | abstractSub (K, depth, I.Dot (Undef, s), S) = I.Nil
(*	  abstractSub (K, depth, s, S) *)
 
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



    (* abstractCtx (K, depth, G) = (G', depth')
       where G' = {{G}}_K

       Invariants:
       If G0 |- G ctx
       and K ||- G
       and |G0| = depth
       then {{K}}, G0 |- G' ctx
       and . ||- G'
       and |G0,G| = depth'
    *)
    fun abstractCtx (K, depth, I.Null) = (I.Null, depth)
      | abstractCtx (K, depth, I.Decl (G, D)) =
        let
	  val (G', depth') = abstractCtx (K, depth, G)
	  val D' = abstractDec (K, depth', (D, I.id))
	in
	  (I.Decl (G', D'), depth'+1)
	end

(*
    fun abstractCtx I.Null = I.Null
      | abstractCtx (I.Decl(G, D)) =  
          let  
	    val K = collectDec (I.Null, (D, I.id), I.Null) 
	  in  
	    I.Decl(abstractCtx(G),  
		  abstractDec(K, 0, (D, I.id)))
	  end  
*)

    (* abstractKPi (K, V) = V'
       where V' = {{K}} V

       Invariant: 
       If   {{K}} |- V : L 
       and  . ||- V

       then V' = {{K}} V
       and  . |- V' : L
       and  . ||- V'
    *)
    fun abstractKPi (I.Null, V) = V
      | abstractKPi (I.Decl (K', EV (I.EVar (_, GX, VX, _))), V) =
        let
          val V' = raiseType (GX, VX) 
	  val V'' = abstractExp (K', 0, (V', I.id))
	  val _ = checkType V''	
	in
	  abstractKPi (K', I.Pi ((I.Dec(NONE, V''), I.Maybe), V))
	end
      | abstractKPi (I.Decl(K', FV (name,V')), V) =
	let
	  val V'' = abstractExp (K', 0, (V', I.id))
	  val _ = checkType V''
	in
	  abstractKPi (K', I.Pi ((I.Dec(SOME(name), V''), I.Maybe), V))
	end

    (* abstractKLam (K, U) = U'
       where U' = [[K]] U

       Invariant: 
       If   {{K}} |- U : V 
       and  . ||- U
       and  . ||- V

       then U' = [[K]] U
       and  . |- U' : {{K}} V
       and  . ||- U'
    *)
    fun abstractKLam (I.Null, U) = U
      | abstractKLam (I.Decl (K', EV (I.EVar (_, GX, VX, _))), U) =
        let
	  val V' = raiseType (GX, VX)
	in
          abstractKLam (K', I.Lam (I.Dec(NONE, abstractExp (K', 0, (V', I.id))), U))
	end
      | abstractKLam (I.Decl (K', FV (name,V')), U) =
	(print ("NAME :" ^ name ^ "\n"); 
 	  abstractKLam (K', I.Lam (I.Dec(SOME(name), abstractExp (K', 0, (V', I.id))), U)))


    fun abstractKCtx (I.Null) = I.Null
      | abstractKCtx (I.Decl (K', EV (I.EVar (_, GX, VX, _)))) =
        let
	  val V' = raiseType (GX, VX)
	  val V'' = abstractExp (K', 0, (V', I.id))
	in
	  I.Decl (abstractKCtx K', I.Dec (NONE, V''))
	end
      | abstractKCtx (I.Decl (K', FV (name, V'))) =
	let
	  val V'' = abstractExp (K', 0, (V', I.id))
	in
	  I.Decl (abstractKCtx K', I.Dec (SOME(name), V''))
	end	


    (* abstractDecImp V = (k', V')   (* rename --cs  (see above) *)

       Invariant: 
       If    . |- V : L
       and   K ||- V

       then  . |- V' : L
       and   V' = {{K}} V
       and   . ||- V'
       and   k' = |K|
    *)
    fun abstractDecImp V =
        let
	  val K = collectExp (I.Null, (V, I.id), I.Null)
	  val constraints = collectConstraints K
          val _ = if (constraints = nil) then () else raise C.Error constraints
	in
	  (I.ctxLength K, abstractKPi (K, abstractExp (K, 0, (V, I.id))))
	end 

    (* abstractDef  (U, V) = (k', (U', V'))

       Invariant: 
       If    . |- V : L
       and   . |- U : V
       and   K1 ||- V
       and   K2 ||- U
       and   K = K1, K2

       then  . |- V' : L
       and   V' = {{K}} V
       and   . |- U' : V'
       and   U' = [[K]] U
       and   . ||- V'
       and   . ||- U'
       and   k' = |K|
    *)
    fun abstractDef (U, V) =
        let
	  val K = collectExp (I.Null, (U, I.id), collectExp (I.Null, (V, I.id), I.Null))
	in
	  (I.ctxLength K, (abstractKLam (K, abstractExp (K, 0, (U, I.id))), 
			   abstractKPi  (K, abstractExp (K, 0, (V, I.id)))))
	end 

    (* closedDec (G, D) = true iff D contains no EVar or FVar *)
    fun closedDec (G, (I.Dec (_, V), s)) = 
      case collectExp (G, (V, s), I.Null)
	of I.Null => true
         | _ => false

    fun closedSub (G, I.Shift _) = true
      | closedSub (G, I.Dot (I.Idx _, s)) = closedSub (G, s)
      | closedSub (G, I.Dot (I.Exp U, s)) = 
      (case collectExp (G, (U, I.id), I.Null)
	 of I.Null => closedSub (G, s)
          | _ => false)

    fun closedExp (G, (U, s)) = 
      case collectExp (G, (U, I.id), I.Null)
	of I.Null => true
         | _ => false

    fun closedCtx I.Null = true
      | closedCtx (I.Decl (G, D)) =
          closedCtx G andalso closedDec (G, (D, I.id))

    fun evarsToK (nil) = I.Null
      | evarsToK (X::Xs) = I.Decl (evarsToK (Xs), EV(X))

    fun KToEVars (I.Null) = nil
      | KToEVars (I.Decl (K, EV(X))) = X::KToEVars (K)
      | KToEVars (I.Decl (K, _)) = KToEVars (K)

    (* collectEVars (G, U[s], Xs) = Xs'
       Invariants:
         G |- U[s] : V
         Xs' extends Xs by new EVars in U[s]
    *)
    fun collectEVars (G, Us, Xs) =
          KToEVars (collectExp (G, Us, evarsToK (Xs)))

    (* abstractKSub (K, U) = s
       where U[s] = [[K]] U

       Invariant: 
       If   {{K}} |- U : V 
       and  . ||- U
       and  . ||- V

       then U[s] = [[K]] U
       and  . |- U[s] : {{K}} V
       and  . ||- U[s]
    *)

    fun abstractKSub (G, I.Null, s) = (G,s)
      | abstractKSub (G, I.Decl (K', EV (I.EVar (_, GX, VX, _))),s) =
        let
	  val V' = raiseType (GX, VX)
	  val G' = I.Decl (G, I.decSub (I.Dec (NONE, abstractExp (K',0, (V', I.id))), s))
	in
          abstractKSub (G', K', I.dot1 s)
	end
      | abstractKSub (G, I.Decl (K', FV (name,V')),s) =
	let
	  val G' = I.Decl (G, I.decSub (I.Dec (SOME(name), V'), s))
	in
	(* I.Exp(abstractExp (K', 0, (V', I.id))), *)
 	  abstractKSub(G', K', I.dot1 s)
	end 

    fun abstractKSub' (G, I.Null, s) = (G, s)
      | abstractKSub' (G, I.Decl (K', EV (E as I.EVar (_, GX, VX, _))),s) =
        let
	  val V' = raiseType (GX, VX)
          val (G',s') = abstractKSub' (G, K', s)
	  val G'' = I.Decl (G', I.decSub (I.Dec (NONE, abstractExp (K',0, (V', I.id))), s))
	in
	  (G'', I.dot1 s')
	end       

      | abstractKSub' (G, I.Decl (K', FV (name,V')),s) =
	let
          val (G',s') = abstractKSub' (G, K', s)
	  val G'' = I.Decl (G', I.decSub (I.Dec (SOME(name), V'), s))
	in
	(* I.Exp(abstractExp (K', 0, (V', I.id))), *)
	  (G'', I.dot1 s')
(* 	  abstractKSub(G', K', I.dot1 s) *)
	end 


       (* lowerAVar (G, V[s]) = (X', U), see lowerEVar *)
    fun lowerAVar (X, G, (I.Pi ((D',_), V'), s')) =
        let
	  val D'' = I.decSub (D', s')
	  val (X', U) = lowerAVar (X, I.Decl (G, D''), Whnf.whnf (V', I.dot1 s'))
	in
	  (X', I.Lam (D'', U))
	end
      | lowerAVar (X, G, Vs') =
        let
(*	  val X' = newEVar (G, EClo Vs') *)
	  val X' = X
	in
	  (X', X')
	end
    (* lowerEVar1 (X, V[s]), V[s] in whnf, see lowerEVar *)
    and (* lowerEVar1 (X, I.EVar (r, G, _, _), (V as I.Pi _, s)) = *)
      lowerEVar1 (X, I.EVar (r, G, _, _), (V as I.Pi _, s)) =
        let 
	  val (X', U) = lowerAVar (X, G, (V,s))
(*	  val _ = r := SOME (U) *)
	in
(*	  X' *)
	  I.EVar(ref (SOME(U)), I.Null, V, ref nil)
	end
      | lowerEVar1 (_, X, _) = X

    (* lowerEVar (X) = X'

       Invariant:
       If   G |- X : {{G'}} P
            X not subject to any constraints
       then G, G' |- X' : P

       Effect: X is instantiated to [[G']] X' if G' is empty
               otherwise X = X' and no effect occurs.
    *)
    and 
      lowerEVar (E, X as I.EVar (r, G, V, ref nil)) = lowerEVar1 (E, X, Whnf.whnf (V, I.id))
      | lowerEVar (E, I.EVar _) =
        (* It is not clear if this case can happen *)
        (* pre-Twelf 1.2 code walk, Fri May  8 11:05:08 1998 *)
        raise Error "abstraction : LowerEVars: Typing ambiguous -- constraint of functional type cannot be simplified"



    fun abstractKSubEVar (G, I.Null, s) = (G, s)
      | abstractKSubEVar (G, I.Decl (K', EV (E as I.EVar (I as (ref NONE), GX, VX, cnstr))),s) =
        let
	  val V' = raiseType (GX, VX) (* redundant ? *)
	  val (G', s') = abstractKSubEVar (G, K', s)
	  val X = lowerEVar1 (E, I.EVar(I, I.Null, V', cnstr), Whnf.whnf(V', I.id)) 
(*	  val X = lowerEVar (E, I.EVar(I, I.Null, V', cnstr)) *)
	in
	  (G', I.Dot(I.Exp(X), s'))      
	end
      | abstractKSubEVar (G, I.Decl (K', EV (I.EVar (ref (SOME U), GX, VX, _))),s) =
        let
	  val (G', s') = abstractKSubEVar (G, K', s)
	  val V' = raiseType (GX, VX)
	  val G'' = I.Decl (G', I.decSub (I.Dec (NONE, abstractExp (K',0, (V', I.id))), s))
	in
	 (print "Should not happen if term is in whnf\n";
	  (G'', I.dot1 s'))
	end
      | abstractKSubEVar (G, I.Decl (K', FV (name,V')),s) =
	let
	  val (G', s') =  abstractKSubEVar (G, K', s)
	  val G'' = I.Decl (G', I.decSub (I.Dec (SOME(name), V'), s))
	in
	(* I.Exp(abstractExp (K', 0, (V', I.id))), *)
	  (G'', I.dot1 s')
	end 


    (* abstractSub' (K, depth, s) = s'      (implicit raising) 

        Invariant:  
        If   G |- s : G1    
       and  |G| = depth 
       and  K ||- s 
       and {{K}}, G |- {{s}}_K : G1
       then Gs, G |- s' : G1    where  s' == {{s}}_K

	 *) 

   (* maybe add depth ? increase depth when going down the substitution ? *)
    fun abstractSub' (K, d, I.Shift (k)) =  
      (* print "\n Shift - implicit raising \n"; ? *)
        if k < d then (I.Dot(I.Idx(k+1), I.Shift (k+1))) else I.Shift(k)
      | abstractSub' (K, d, I.Dot (I.Idx (k), s)) =
	I.Dot(I.Idx(k),abstractSub' (K, d, s))
      | abstractSub' (K, d, I.Dot (I.Exp (U), s)) =
	I.Dot(I.Exp(abstractExp (K, d, (U, I.id))), 
	      abstractSub' (K, d, s)) 


    fun deconstructPi (G, I.Pi((D,_), U)) = 
          deconstructPi (I.Decl(G, D), U)
      | deconstructPi (G, U) = (G, U)
   
  in

    (* abstractECloCtx (G, U) = (D', G', U', Pi G'. U')
      
       if G |- U 

       then 
          
          {{K}} |-  Pi G.U where K contains all free vars from G and U
          D' |- Pi G'. U' 
          D', G' |- U'

       *) 

    val abstractECloCtx = (fn (G, U) => 
			   let
			     val V = raiseType (G, U)
			     val K = collectExp(I.Null, (V, I.id), I.Null) 
			     val (Gs',_) = abstractKSub' (I.Null, K, I.id)  
			     val V' = abstractExp (K, 0, (V,I.id)) 
			     val Vpi = abstractKPi (K, V') 
			     val (Gdp', U') = deconstructPi (I.Null, V')   
			   in 
			     (Gs', Gdp', U', Vpi) 
			   end)

  (* abstractEVarCtx (G, p, s) = (G', D', U', s')

     if G |- p[s]
        and s contains free variables X_n .... X_1
     then 
        
       D', G' |- U'  
       where D' is the abstraction over 
       the free vars X_n .... X_1
 
       and s' is a substitution the free variables
            X_n .... X_1, s.t. 

       G' |- s' : D', G'        

       G' |- U'[s']  is equivalent to G |- p[s]

       Note: G' and U' are possibly strengthened
   *)

    val abstractEVarCtx = 
      (fn (G, p, s) => 
       let
	 (* Kdp contains all EVars in G,  G0' = G  *)	
	 val (G0', Kdp) = collectCtx (I.Null, G, I.Null)          	 
	 (* K contains all EVars in (p,s) *)
	 val K = collectExp(G, (p, s), Kdp)
	 (* d = length(G) *)
	 val (G', d) = abstractCtx(K, 0, G)
	 val U' = abstractExp(K, d, (p,s))
	 (* could be done nicer -bp *)
	 val (D',I.Shift(0)) = abstractKSub' (I.Null, K, I.id)  
	 val (_,s') = abstractKSubEVar (I.Null, K, I.id)

	 val _ = if (!Global.chatter) >= 6 then 
	       (print ("\nStrengthen Ctx\n ORIGINAL : \n ");
		print (Print.expToString(I.Null, 
					 raiseType(concat(G', D'), U')) 
		       ^ "\n"))
	       else 
		 ()
	 val (G', ss, s') =  if (!strengthen) then 
 	                       let
				 val w' = weaken (G', I.targetFam U')
				 val iw = Whnf.invert w' 
				 val G' = Whnf.strengthen (iw, G')
			       in		
				 (G', iw, s')
			       end
			      else 
				(G', I.id, s')

	 val _ = if (!Global.chatter) >= 6 then 
	       (print ("\nStrengthed \n ");
		print (Print.expToString(I.Null, 
					 raiseType(concat(G',D'), I.EClo(U', ss)))
		       ^ "\n");
		print ("\n EVar str. goal \n ");
		print (Print.expToString(I.Null, 
					 I.EClo(raiseType(G', I.EClo(U', ss)), s'))
		       ^ "\n"))
	       else 
		 ()
       in 		
	 (G', D', I.EClo(U', ss), s')
       end)


(* redundancy in the way we abstractAnswSub
    bp Thu Feb 21 11:17:07 2002

 *)


  (* abstractAnswSub s = (Delta, s')
    
   if G |- s : Delta', G 
      s may contain free variables
    
   then 
  
    Delta, G |- s' : Delta', G
    where Delta contains all the 
    free variables from s

   *)
    val abstractAnswSub = 
      (fn s => 
       let
	 val K = collectSub(I.Null, s, I.Null) 
	 val s' = abstractSub' (K, 0, s) 
	 val (G1,_) = abstractKSub' (I.Null, K, I.id)  
       in 
	 (G1, s')
       end)

    val abstractAnswSub' = 
      (fn (G, d, s) => 
       let
	 val K = collectSub' (G, s, I.Null) 
	 val s' = abstractSub' (K, d, s) 
	 val (G1,_) = abstractKSub' (I.Null, K, I.id)  
       in 
	 (G1, s')
       end)


(* abstractAnsw (D, s) = (Delta, s')
    
   if D, G |- s : Delta', G 
      s may contain free variables
    
   then 
  
    Delta, D, G |- s' : Delta', G
    where Delta contains all the 
    free variables from s

   *)
(* bp Tue Feb 19 23:35:30 2002 ??? don't understand this function *)
   val abstractAnsw = 
      (fn (D, s) => 
       let
	 (* val d = I.ctxLength(D) *)
	 val (G0', Kus) = collectCtx (I.Null, D, I.Null)
	 val K = collectSub(D, s, Kus) 
	 val (Gus', d) = abstractCtx(K, 0, D)
	 val s' = abstractSub' (K, d , s)
	 val (D1,_) = abstractKSub' (I.Null, K, I.id)  
       in 
	 (*  D1', D |- s' : D', G  *)
	 (concat(Gus',D1), s')
       end)


    (*
     If G |- M 
        G |- p[s']

	K contains all the existential variables of
          G and p[s']

        K is partially instantiated

	s is a substitution only containing free vars 
           X_n . ... . X_2 . X_1

            G' |- s : D', G'
	D', G' |- u
            G' |- u[s]	

      then 
        
        after computation: 

	D1, G' |- s1 : D', G'
	D1, G' | u[s1]

     *)

    val raiseType = (fn (G, U) => 
		       raiseType (G, U)
			   )

    val collectEVars = collectEVars
  end
end;  (* functor AbstractTabled *)



