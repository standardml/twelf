(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)

functor Abstract (structure IntSyn' : INTSYN
		  structure Whnf    : WHNF
		    sharing Whnf.IntSyn = IntSyn'
		  structure Unify   : UNIFY
		    sharing Unify.IntSyn = IntSyn'
		  structure Constraints : CONSTRAINTS
		    sharing Constraints.IntSyn = IntSyn')
  : ABSTRACT =
struct

  structure IntSyn = IntSyn'
    
  exception Error of string
    
  local

    structure I = IntSyn
    structure C = Constraints
      
    (* Intermediate Data Structure *)

    datatype EFVar =
      EV of I.Exp option ref * I.Exp	(* Y ::= (X , {G} V)  if G |- X : V *)
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
    fun eqEVar (I.EVar (r1, _, _, _)) (EV (r2,  _)) = (r1 = r2)
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

    (* occursInExp (k, U) = B, 

       Invariant:
       If    U in nf 
       then  B iff k occurs in U
    *)
    fun occursInExp (k, I.Uni _) = false
      | occursInExp (k, I.Pi (DP, V)) = occursInDecP (k, DP) orelse occursInExp (k+1, V)
      | occursInExp (k, I.Root (H, S)) = occursInHead (k, H) orelse occursInSpine (k, S)
      | occursInExp (k, I.Lam (D, V)) = occursInDec (k, D) orelse occursInExp (k+1, V)
      (* no case for Redex, EVar, EClo *)

    and occursInHead (k, I.BVar (k')) = (k = k')
      | occursInHead (k, I.Const _) = false
      | occursInHead (k, I.Def _) = false
      | occursInHead (k, I.Skonst _) = false
      (* no case for FVar *)
      (* no case for Skonst *)

    and occursInSpine (_, I.Nil) = false
      | occursInSpine (k, I.App (U, S)) = occursInExp (k, U) orelse occursInSpine (k, S)
      (* no case for SClo *)

    and occursInDec (k, I.Dec (_, V)) = occursInExp (k, V)
    and occursInDecP (k, (D, _)) = occursInDec (k, D)

    (* piDepend ((D,P), V) = Pi ((D,P'), V)
       where P' = Maybe if D occurs in V, P' = No otherwise 
    *)
    (* optimize to have fewer traversals? -cs *)
    (* pre-Twelf 1.2 code walk Fri May  8 11:17:10 1998 *)
    fun piDepend (DPV as ((D, I.No), V)) = I.Pi DPV
      | piDepend ((D, I.Maybe), V) = 
        if occursInExp (1, V)
	  then I.Pi ((D, I.Maybe), V)
	else I.Pi ((D, I.No), V)

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
      | collectExpW (G, (X as I.EVar (r, GX, V, Cnstr), s), K) =
	  if exists (eqEVar X) K
	    then collectSub(G, s, K)
	  else let
	         val _ = checkEmpty Cnstr
		 val V' = raiseType (GX, V)
	       in
		 collectSub(G, s, I.Decl (collectExp (I.Null, (V', I.id), K), EV(r, V')))
	       end
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

    (* abstractEVar (K, depth, X) = C'
     
       Invariant:
       If   G |- X : V
       and  |G| = depth
       and  X occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
    fun abstractEVar (I.Decl (K', EV (r', _)), depth, X as I.EVar (r, _, _, _)) =
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
      | abstractKPi (I.Decl (K', EV (_, V')), V) =
        let
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
      | abstractKLam (I.Decl (K', EV (_,V')), U) =
          abstractKLam (K', I.Lam (I.Dec(NONE, abstractExp (K', 0, (V', I.id))), U))
      | abstractKLam (I.Decl (K', FV (name,V')), U) =
 	  abstractKLam (K', I.Lam (I.Dec(SOME(name), abstractExp (K', 0, (V', I.id))), U))

    (* abstractDec V = (k', V')

       Invariant: 
       If    . |- V : L
       and   K ||- V

       then  . |- V' : L
       and   V' = {{K}} V
       and   . ||- V'
       and   k' = |K|
    *)
    fun abstractDec V =
        let
	  val K = collectExp (I.Null, (V, I.id), I.Null)
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

  in
    val piDepend = piDepend
    val closedDec = closedDec

    val abstractDec = abstractDec
    val abstractDef = abstractDef
  end
end;  (* functor Abstract *)
