(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)

functor Abstract ((*! structure IntSyn' : INTSYN !*)
		  structure Whnf    : WHNF
		  (*! sharing Whnf.IntSyn = IntSyn' !*)
		  structure Unify   : UNIFY
		  (*! sharing Unify.IntSyn = IntSyn' !*)
		  structure Constraints : CONSTRAINTS
		  (*! sharing Constraints.IntSyn = IntSyn' !*)
		    )
  : ABSTRACT =
struct

  (*! structure IntSyn = IntSyn' !*)
    
  exception Error of string
    
  local

    structure I = IntSyn
    structure C = Constraints
      
    (* Intermediate Data Structure *)

    datatype EFLVar =
      EV of I.Exp			(* Y ::= X         for  GX |- X : VX *)
    | FV of string * I.Exp		(*     | (F, V)        if . |- F : V *)
    | LV of I.Block                     (*     | L             if . |- L in W *) 


    (*
       We write {{K}} for the context of K, where EVars, FVars, LVars have
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
      | collectConstraints (I.Decl (G, LV _)) = collectConstraints G

    (* checkConstraints (K) = ()
       Effect: raises Constraints.Error(C) if K contains unresolved constraints
    *)
    fun checkConstraints (K) =
        let
	  val constraints = collectConstraints K
	  val _ = case constraints
	            of nil => ()
		     | _ => raise C.Error (constraints)
	in
	  ()
	end

    (* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)
    (*
    fun checkEmpty (nil) = ()
      | checkEmpty (Cnstr) =
        (case C.simplify Cnstr
	   of nil => ()
	    | _ => raise Error "Typing ambiguous -- unresolved constraints")
    *)
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

    (* eqLVar L Y = B
       where B iff X and Y represent same variable
    *)
    fun eqLVar (I.LVar (r1, _)) (LV (I.LVar (r2, _))) = (r1 = r2)
      | eqLVar _ _ = false


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
      | occursInHead (k, I.Proj _, DP) = DP   
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

    (* raiseTerm (G, U) = [[G]] U

       Invariant:
       If G |- U : V
       then  . |- [[G]] U : {{G}} V

       All abstractions are potentially dependent.
    *)
    fun raiseTerm (I.Null, U) = U
      | raiseTerm (I.Decl (G, D), U) = raiseTerm (G, I.Lam (D, U))

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
      | collectExpW (G, (I.Root (I.Proj (L as I.LVar (r, (l, t)), i), S), s), K) =
	if exists (eqLVar L) K
	  (* note: don't collect t again below *)
	  (* was: collectSpine (G, (S, s), collectSub (I.Null, t, K)) *)
	  (* Sun Dec 16 10:54:52 2001 -fp !!! *)
	  then collectSpine (G, (S, s), K)
	else 
	  collectSpine (G, (S, s), I.Decl (collectSub (I.Null, t, K), LV L))
      | collectExpW (G, (I.Root (_ , S), s), K) =
	  collectSpine (G, (S, s), K)
      | collectExpW (G, (I.Lam (D, U), s), K) =
	  collectExp (I.Decl (G, I.decSub (D, s)), (U, I.dot1 s), collectDec (G, (D, s), K))
      | collectExpW (G, (X as I.EVar (r, GX, V, cnstrs), s), K) =
	if exists (eqEVar X) K
	  then collectSub(G, s, K)
	else let
	       (* val _ = checkEmpty !cnstrs *)
	       val V' = raiseType (GX, V) (* inefficient *)
	       val K' = collectExp (I.Null, (V', I.id), K)
	     in
	       collectSub(G, s, I.Decl (K', EV (X)))
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
      | collectDec (G, (I.BDec (_, (_, t)), s), K) =
	  (* . |- t : Gsome, so do not compose with s *)
	  (* Sat Dec  8 13:28:15 2001 -fp *)
	  collectSub (I.Null, t, K)

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
      | collectSub (G, I.Dot (I.Block B, s), K) =
	  collectSub (G, s, collectBlock (B, K))
    (* next case should be impossible *)
    (*
      | collectSub (G, I.Dot (I.Undef, s), K) =
          collectSub (G, s, K)
    *)

    (* collectBlock (B, K) where . |- B block *)
    and collectBlock (I.LVar (ref (SOME B), _), K) =
          collectBlock (B, K)
      | collectBlock (L as I.LVar (_, (l, t)), K) = 
        if exists (eqLVar L) K
	  then collectSub (I.Null, t, K)
	else I.Decl (collectSub (I.Null, t, K), LV L)
    (* | collectBlock (G, I.Bidx _, K) = K *)
    (* should be impossible: Fronts of substitutions are never Bidx *)
    (* Sat Dec  8 13:30:43 2001 -fp *)

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

    (* collectCtxs (G0, Gs, K) = K'
       Invariant: G0 |- G1,...,Gn ctx where Gs = [G1,...,Gn]
       and K' = K, K'' where K'' contains all EVars and FVars in G1,...,Gn
    *)
    fun collectCtxs (G0, nil, K) = K
      | collectCtxs (G0, G::Gs, K) =
        let
	  val (G0', K') = collectCtx (G0, G, K)
	in
          collectCtxs (G0', Gs, K')
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
(*      | abstractEVar (I.Decl (K', FV (n', _)), depth, X) = 
	  abstractEVar (K', depth+1, X) remove later --cs*)
      | abstractEVar (I.Decl (K', _), depth, X) = 
	  abstractEVar (K', depth+1, X)

    (* abstractFVar (K, depth, F) = C'
     
       Invariant:
       If   G |- F : V
       and  |G| = depth
       and  F occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
    fun abstractFVar (I.Decl(K', FV (n', _)), depth, F as I.FVar (n, _, _)) = 
	  if n = n' then I.BVar (depth+1)
	  else abstractFVar (K', depth+1, F)
(*      | abstractFVar (I.Decl(K', EV _), depth, F) =
  	  abstractFVar (K', depth+1, F) remove later --cs *)
      | abstractFVar (I.Decl(K', _), depth, F) =
  	  abstractFVar (K', depth+1, F)
       
    (* abstractLVar (K, depth, L) = C'
     
       Invariant:
       If   G |- L : V
       and  |G| = depth
       and  L occurs in K  at kth position (starting at 1)
       then C' = Bidx (depth + k)
       and  {{K}}, G |- C' : V
    *)
    fun abstractLVar (I.Decl(K', LV (I.LVar (r', _))), depth, L as I.LVar (r, _)) = 
	  if r = r' then I.Bidx (depth+1)
	  else abstractLVar (K', depth+1, L)
      | abstractLVar (I.Decl(K', _), depth, L) =
  	  abstractLVar (K', depth+1, L)
      
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
      | abstractExpW (K, depth, (I.Root (I.Proj (L as I.LVar _, i), S), s)) =
	  I.Root (I.Proj (abstractLVar (K, depth, L), i),  
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

    (* abstractSOME (K, s) = s'
       s' = {{s}}_K

       Invariant:
       If    . |- s : Gsome    
       and   K is internal context in dependency order
       and   K ||- s
       then  {{K}} |- s' : Gsome  --- not changing domain of s'

       Update: modified for globality invariant of . |- t : Gsome
       Sat Dec  8 13:35:55 2001 -fp
    *)
    fun abstractSOME (K, I.Shift 0) = (* n = 0 by invariant, check for now *)
          I.Shift (I.ctxLength(K))
      | abstractSOME (K, I.Dot (I.Idx k, s)) = 
          I.Dot (I.Idx k, abstractSOME (K, s))
      | abstractSOME (K, I.Dot (I.Exp U, s)) =
	  I.Dot (I.Exp (abstractExp (K, 0, (U, I.id))), abstractSOME (K, s))
      | abstractSOME (K, I.Dot (I.Block (L as I.LVar _), s)) =
	  I.Dot (I.Block (abstractLVar (K, 0, L)), abstractSOME (K, s))
      (* I.Block (I.Bidx _) should be impossible as head of substitutions *)

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

    (* abstractCtxlist (K, depth, [G1,...,Gn]) = [G1',...,Gn']
       where Gi' = {{Gi}}_K

       Invariants:
       if G0 |- G1,...,Gn ctx 
       and K ||- G1,...,Gn
       and |G0| = depth
       then {{K}}, G0 |- G1',...,Gn' ctx
       and . ||- G1',...,Gn'
    *)
    fun abstractCtxlist (K, depth, nil) = nil
      | abstractCtxlist (K, depth, G::Gs) =
        let
	  val (G', depth') = abstractCtx (K, depth, G)
	  val Gs' = abstractCtxlist (K, depth', Gs)
	in
	  G'::Gs'
	end

    (* dead code under new reconstruction -kw
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
          (* enforced by reconstruction -kw
	  val _ = checkType V''	*)
	in
	  abstractKPi (K', I.Pi ((I.Dec(NONE, V''), I.Maybe), V))
	end
      | abstractKPi (I.Decl (K', FV (name,V')), V) =
	let
	  val V'' = abstractExp (K', 0, (V', I.id))
          (* enforced by reconstruction -kw
	  val _ = checkType V'' *)
	in
	  abstractKPi (K', I.Pi ((I.Dec(SOME(name), V''), I.Maybe), V))
	end
      | abstractKPi (I.Decl (K', LV (I.LVar (r, (l, t)))), V) =
	let
	  val t' = abstractSOME (K', t)	  
	in
	  abstractKPi (K', I.Pi ((I.BDec (NONE, (l, t')), I.Maybe), V))
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
 	  abstractKLam (K', I.Lam (I.Dec(SOME(name), abstractExp (K', 0, (V', I.id))), U))

    fun abstractKCtx (I.Null) = I.Null
      | abstractKCtx (I.Decl (K', EV (I.EVar (_, GX, VX, _)))) =
        let
	  val V' = raiseType (GX, VX)
	  val V'' = abstractExp (K', 0, (V', I.id))
          (* enforced by reconstruction -kw
	  val _ = checkType V''	*)
	in
	  I.Decl (abstractKCtx K', I.Dec (NONE, V''))
	end
      | abstractKCtx (I.Decl (K', FV (name, V'))) =
	let
	  val V'' = abstractExp (K', 0, (V', I.id))
          (* enforced by reconstruction -kw
	  val _ = checkType V'' *)
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
	  val _ = checkConstraints (K)
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
	  val _ = checkConstraints K
	in
	  (I.ctxLength K, (abstractKLam (K, abstractExp (K, 0, (U, I.id))), 
			   abstractKPi  (K, abstractExp (K, 0, (V, I.id)))))
	end 

    (* abstractCtxs [G1,...,Gn] = G0, [G1',...,Gn']
       Invariants:
       If . |- G1,...,Gn ctx
          K ||- G1,...,Gn for some K
       then G0 |- G1',...,Gn' ctx for G0 = {{K}}
       and G1',...,Gn' nf
       and . ||- G1',...,Gn' ctx
    *)
    fun abstractCtxs (Gs) =
        let
	  val K = collectCtxs (I.Null, Gs, I.Null)
	  val _ = checkConstraints K
	in
	  (abstractKCtx (K), abstractCtxlist (K, 0, Gs))
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

  in

    val raiseType = raiseType
    val raiseTerm = raiseTerm

    val piDepend = piDepend
    val closedDec = closedDec
    val closedSub = closedSub
    val closedExp = closedExp 

    val abstractDecImp = abstractDecImp
    val abstractDef = abstractDef
    val abstractCtxs = abstractCtxs

    val collectEVars = collectEVars

    val closedCtx = closedCtx
  end
end;  (* functor Abstract *)
