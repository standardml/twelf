(* Meta Theorem Prover abstraction : Version 1.3 *)
(* Author: Frank Pfenning, Carsten Schuermann *)

functor MTPAbstract (structure IntSyn' : INTSYN
		     structure FunSyn : FUNSYN
		       sharing FunSyn.IntSyn = IntSyn'
		     structure StateSyn' : STATESYN
		       sharing StateSyn'.FunSyn = FunSyn
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
    structure F = FunSyn
    structure S = StateSyn
    structure C = Constraints
      
    (* Intermediate Data Structure *)

    datatype EBVar =
      EV of I.Exp option ref * I.Exp * S.Tag * int
					(* y ::= (X , {G2} V)  if {G1, G2 |- X : V 
					  |G1| = d *)
    | BV of I.Dec * S.Tag


    (*
       We write {{K}} for the context of K, where EVars and BVars have
       been translated to declarations and their occurrences to BVars.
       We write {{U}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts G, any K is implicitly assumed to be
       well-formed and in dependency order.

       We write  K ||- U  if all EVars and BVars in U are collected in K.
       In particular, . ||- U means U contains no EVars or BVars.  Similarly,
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
    fun eqEVar (I.EVar (r1, _, _, _)) (EV (r2, _, _, _)) = (r1 = r2)
      | eqEVar _ _ = false


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

    fun restore (0, _) = I.Null
      | restore (n, I.Decl (G, D)) = I.Decl (restore (n - 1, G), D)

    (* collectExpW (T, d, G, (U, s), K) = K'

       Invariant: 
       If    G |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
             (enforced by extended occurs-check for BVars in Unify)
       and   K' = K, K''
	     where K'' contains all EVars and BVars in (U,s)
    *)
    (* Possible optimization: Calculate also the normal form of the term *)
    fun collectExpW (T, d, G, (I.Uni L, s), K) = K
      | collectExpW (T, d, G, (I.Pi ((D, _), V), s), K) =
          collectExp (T, d, I.Decl (G, I.decSub (D, s)), (V, I.dot1 s), collectDec (T, d, G, (D, s), K))
      | collectExpW (T, d, G, (I.Root (_ , S), s), K) =
	  collectSpine (S.decrease T, d, G, (S, s), K)
      | collectExpW (T, d, G, (I.Lam (D, U), s), K) =
	  collectExp (T, d, I.Decl (G, I.decSub (D, s)), (U, I.dot1 s), collectDec (T, d, G, (D, s), K))
      | collectExpW (T, d, G, (X as I.EVar (r, GdX, V, Cnstr), s), K) =
	  if exists (eqEVar X) K
	    then collectSub (T, d, G, s, K)
	  else let
	         val GX = restore (I.ctxLength GdX - d, GdX)   (* optimization possible for d = 0 *)
	         val _ = checkEmpty Cnstr
		 val w = weaken (GX, I.targetFam V)
		 val iw = Whnf.invert w
		 val GX' = Whnf.strengthen (iw, GX)
		 val V' = raiseType (GX', I.EClo (V, iw))
		 val X' as I.EVar (r', _, _, _) = I.newEVar (GX', I.EClo (V, iw))
		 val _ = Trail.instantiateEVar (r, I.EClo (X', w))
	       in
		 collectSub (T, d, G, s, I.Decl (collectExp (T, d, I.Null, (V', I.id), K), EV (r', V', T, d)))
	       end
      (* No other cases can occur due to whnf invariant *)

    (* collectExp (T, d, G, (U, s), K) = K' 
       
       same as collectExpW  but  (U,s) need not to be in whnf 
    *) 
    and collectExp (T, d, G, Us, K) = collectExpW (T, d, G, Whnf.whnf Us, K)

    (* collectSpine (T, d, G, (S, s), K) = K' 

       Invariant: 
       If    G |- s : G1     G1 |- S : V > P
       then  K' = K, K''
       where K'' contains all EVars and BVars in (S, s)
     *)
    and collectSpine (T, d, G, (I.Nil, _), K) = K
      | collectSpine (T, d, G, (I.SClo(S, s'), s), K) = 
          collectSpine (T, d, G, (S, I.comp (s', s)), K)
      | collectSpine (T, d, G, (I.App (U, S), s), K) =
	  collectSpine (T, d, G, (S, s), collectExp (T, d, G, (U, s), K))

    (* collectDec (T, d, G, (x:V, s), K) = K'

       Invariant: 
       If    G |- s : G1     G1 |- V : L
       then  K' = K, K''
       where K'' contains all EVars and BVars in (V, s)
    *)
    and collectDec (T, d, G, (I.Dec (_, V), s), K) =
          collectExp (T, d, G, (V, s), K)

    (* collectSub (T, d, G, s, K) = K' 

       Invariant: 
       If    G |- s : G1    
       then  K' = K, K''
       where K'' contains all EVars and BVars in s
    *)
    and collectSub (T, d, G, I.Shift _, K) = K
      | collectSub (T, d, G, I.Dot (I.Idx _, s), K) = collectSub (T, d, G, s, K)
      | collectSub (T, d, G, I.Dot (I.Exp (U), s), K) =
	  collectSub (T, d, G, s, collectExp (T, d, G, (U, I.id), K))

    (* abstractEVar (K, depth, X) = C'
     
       Invariant:
       If   G |- X : V
       and  |G| = depth
       and  X occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
    fun abstractEVar (I.Decl (K', EV (r', _, _, d)), depth, X as I.EVar (r, _, _, _)) =
        if r = r' then (I.BVar (depth+1), d)
	else abstractEVar (K', depth+1, X)
      | abstractEVar (I.Decl (K', BV _), depth, X) = 
	  abstractEVar (K', depth+1, X)



    (* lookupBV (A, i) = k'

       Invariant:

       If   A ||- V
       and  G |- V type
       and  G [x] A |- i : V'
       then ex a substititution  G x A |- s : G [x] A
       and  G x A |- k' : V''
       and  G x A |- V' [s] = V'' : type
    *)
    fun lookupBV (K, i) =
      let 
	fun lookupBV' (I.Decl (K, EV (r, V, _, _)), i, k) = 
	      lookupBV' (K, i, k+1)
	  | lookupBV' (I.Decl (K, BV _), 1, k) = k
	  | lookupBV' (I.Decl (K, BV _), i, k) =
	      lookupBV' (K, i-1, k+1)
	(* lookupBV' I.Null cannot occur by invariant *)
      in
	lookupBV' (K, i, 1)
      end


 
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
      | abstractExpW (K, depth, (I.Root (H as I.BVar k, S), s)) = (* s = id *)
	  if k > depth then 
	    let 
	      val k' = lookupBV (K, k-depth)
	    in
	      I.Root (I.BVar (k'+depth), abstractSpine (K, depth, (S, s)))
	    end
	  else 
	  I.Root (H, abstractSpine (K, depth, (S, s)))   
      | abstractExpW (K, depth, (I.Root (H, S) ,s)) =
	  I.Root (H, abstractSpine (K, depth, (S, s)))   
      | abstractExpW (K, depth, (I.Lam (D, U), s)) =
          I.Lam (abstractDec (K, depth, (D, s)),
		 abstractExp (K, depth + 1, (U, I.dot1 s)))
      | abstractExpW (K, depth, (X as I.EVar _, s)) =
	  let 
	    val (H, d) = abstractEVar (K, depth, X)
	  in
	    I.Root (H, abstractSub (K, depth, s, I.Nil))
	  end

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

       BUG: non-local BVars must be correctly abstracted!!!! -cs 
    *)
    fun abstractCtx (I.Null) = (I.Null, I.Null)
      | abstractCtx (I.Decl (K', EV (_, V', T, _))) =
        let
	  val S.Lemma (b, F.Ex (_, F.True)) = T      
	  val V'' = abstractExp (K', 0, (V', I.id))
	  val _ = checkType V''
	  val (G', B') = abstractCtx K'
	  val D' = I.Dec (NONE, V'')
	  val T' = S.Lemma (b, F.Ex (D', F.True))
	in
	  (I.Decl (G', D'), I.Decl (B', T'))
	end
      | abstractCtx (I.Decl (K', BV (D, T))) =
        let
	  val D' = abstractDec (K', 0, (D, I.id))
	  val (G', B') = abstractCtx K'
	in
	  (I.Decl (G', D'), I.Decl (B', T))
	end



    (* abstractGlobalSub (K, s, B) = s'
      
       Invariant:
       If   K > G   aux context
       and  G |- s : G'
       then K |- s' : G'
    *)


    fun abstractGlobalSub (K, I.Shift _, I.Null) = I.Shift (I.ctxLength K)
      | abstractGlobalSub (K, I.Shift n, B as I.Decl _) =
	  abstractGlobalSub (K, I.Dot (I.Idx (n+1), I.Shift (n+1)), B)
      | abstractGlobalSub (K, I.Dot (I.Idx k, s'), I.Decl (B, T as S.Parameter _)) =
          I.Dot (I.Idx (lookupBV (K, k)), abstractGlobalSub (K, s', B))
      | abstractGlobalSub (K, I.Dot (I.Exp U, s'), I.Decl (B, T as S. Lemma _)) =
          I.Dot (I.Exp (abstractExp (K, 0, (U, I.id))), abstractGlobalSub (K, s', B))



    (* collectGlobalSub (G0, s, B, collect) = collect'
       
       Invariant: 
       If   |- G0 ctx
       and  |- G ctx
       and  G |- B tags
       and  G0 |- s : G 
       and  collect is a function which maps
	       (d, K)  (d expresses the number of parameters in K, |- K aux ctx)
	    to K'      (|- K' aux ctx, which collects all EVars in K)
    *)
    fun collectGlobalSub (G0, I.Shift _, I.Null, collect) =  collect 
      | collectGlobalSub (G0, s, B as I.Decl (_, S.Parameter (SOME l)), collect) = 
        let
	  val F.LabelDec (name, _, G2) = F.labelLookup l
	in
	  skip (G0, List.length G2, s, B, collect)
	end
      | collectGlobalSub (G0, I.Dot (I.Exp (U), s), I.Decl (B, T), collect) =
	  collectGlobalSub (G0, s, B, fn (d, K) => 
		       collect (d, collectExp (T, d, G0, (U, I.id), K)))
    (* no cases for (G0, s, B as I.Decl (_, S.Parameter NONE), collect) *)


    and skip (G0, 0, s, B, collect) = collectGlobalSub (G0, s, B, collect)
      | skip (I.Decl (G0, D), n, s, I.Decl (B, T as S.Parameter _), collect) =
          skip (G0, n-1, I.invDot1 s, B, fn (d, K) => collect (d+1, I.Decl (K, BV (D, T))))
      

    (* abstractNew ((G0, B0), s, B) = ((G', B'), s')

       Invariant: 
       If   . |- G0 ctx
       and  G0 |- B0 tags
       and  G0 |- s : G
       and  G |- B tags
       then . |- G' = G1, Gp, G2
       and  G' |- B' tags
       and  G' |- s' : G
    *)
    fun abstractNew ((G0, B0), s, B) =
        let
	  val cf = collectGlobalSub (G0, s, B, fn (_, K') => K')
	  val K = cf (0, I.Null)
	in
	  (abstractCtx K, abstractGlobalSub (K, s, B))
	end 




    (* abstractSub (t, B1, (G0, B0), s, B) = ((G', B'), s')

       Invariant: 
       If   . |- t : G1
       and  G1 |- B1 tags

       and  G0 |- B0 tags
       and  G0 |- s : G
       and  G |- B tags
       then . |- G' = G1, G0, G2
       and  B' |- G' tags
       and  G' |- s' : G
    *)
    fun abstractSubAll (t, B1, (G0, B0), s, B) =
        let
	  (* skip'' (K, (G, B)) = K'
	   
	     Invariant:
	     If   G = x1:V1 .. xn:Vn 
	     and  G |- B = <param> ... <param> tags
	     then  K' = K, BV (x1) .. BV (xn)
	  *)

	  fun skip'' (K, (I.Null, I.Null)) = K
	    | skip'' (K, (I.Decl (G0, D), I.Decl(B0, T))) = I.Decl (skip'' (K, (G0, B0)), BV (D, T))

	  val collect2 = collectGlobalSub (G0, s, B, fn (_, K') => K')
	  val collect0 = collectGlobalSub (I.Null, t, B1, fn (_, K') => K')
	  val K0 = collect0 (0, I.Null)
	  val K1 = skip'' (K0, (G0, B0))
	  val K = collect2 (I.ctxLength G0, K1)
	in
	  (abstractCtx K, abstractGlobalSub (K, s, B))
	end 


(*
    (* abstractSub (t, (G0, B0), s, B) = ((G', B'), s')

       Invariant: 
       If   . |- t : G0
       and  G0 |- B0 tags
       and  G0 |- s : G
       and  G |- B tags
       then . |- G' = G1, G0, G2
       and  B' |- G' tags
       and  G' |- s' : G
    *)
    fun abstractSubAll (t, (G0, B0), s, B) =
        let

	  (* collectSub (s, B) = (d', K')
	   
	     Invariant:
	     G1, G2 |- s : G 
  	     |- G1 : ctx (only context blocks)
	     |- G2 : ctx (only context blocks)
	     G |- B tags
	     then d' = |G1|
	     and  K' is a auxiliary EVar context
	    *)
(*	  fun collectSub' (I.Null, I.Shift 0, _, collect) = (0, collect (0, I.Null))
	    | collectSub' (G0, s, B as I.Decl (_, S.Parameter (SOME l)), collect) = 
	      let
		val F.LabelDec (name, _, G2) = F.labelLookup l
		val (d, K) = skip (G0, List.length G2, s, B)
	      in
		(d, collect (d, K))
	      end
	    | collectSub' (G0, I.Dot (I.Exp (U), s), I.Decl (B, T), collect) =
	        collectSub' (G0, s, B, fn (d', K') => 
			     let 
			       val K'' = collect (d', K')
			     in
			       collectExp (T, d', G0, (U, I.id), K'')
			     end)
	    (* no cases for (G0, s, B as I.Decl (_, S.Parameter NONE), collect) *)




	  and skip (G0, 0, s, B) = collectSub' (G0, s, B, fn (_, K') => K')
	    | skip (I.Decl (G0, D), n, s, I.Decl (B, T as S.Parameter _)) =
	      let 
		val (d, K) = skip (G0, n-1, I.invDot1 s, B)
	      in
	        (d + 1, I.Decl (K, BV (D, T)))
	      end
*)

	  fun collectSub' (G0, I.Shift _, _, collect) = (fn (d, K) => collect (d, K))
	    | collectSub' (G0, s, B as I.Decl (_, S.Parameter (SOME l)), collect) = 
	      let
		val F.LabelDec (name, _, G2) = F.labelLookup l
	      in
		skip (G0, List.length G2, s, B, collect)
	      end
	    | collectSub' (G0, I.Dot (I.Exp (U), s), I.Decl (B, T), collect) =
	        collectSub' (G0, s, B, fn (d, K) => 
			       collect (d, collectExp (T, d, G0, (U, I.id), K)))
	    | collectSub' (_, I.Dot (I.Idx _, _), I.Decl (B, S.Lemma _), _) = raise Domain 
(*  shouldn't occur *)

	    (* no cases for (G0, s, B as I.Decl (_, S.Parameter NONE), collect) *)


	  and skip (G0, 0, s, B, collect) = collectSub' (G0, s, B, collect)
	    | skip (I.Decl (G0, D), n, s, I.Decl (B, T as S.Parameter _), collect) =
	        skip (G0, n-1, I.invDot1 s, B, fn (d, K) => collect (d+1, I.Decl (K, BV (D, T))))

(* ----- *)

          (* collectSub'' (G0, s, B, collect) = collect'
	     
	     Invariant: 
	     If   G0 |- s : G
	     and  G |- B tags
	     and  collect extends a given K by EVars/BVars
	     then collect' extends a given K according to K
	            and adds the ones in s
	  *)

	  fun collectSub'' (G0, I.Shift _, _, collect) = collect
	    | collectSub'' (G0, I.Dot (I.Exp (U), s), I.Decl (B, T), collect) =
	        collectSub'' (G0, s, B, fn (d', K') => 
			     let 
			       val K'' = collect (d', K')
			     in
			       collectExp (T, d', G0, (U, I.id), K'')
			     end)
(*	    | collectSub'' (G0, I.Dot (I.Idx _, s), I.Decl (B, T), collect) = 
		collectSub'' (G0, s, B, collect) *)
	    (* no cases for (G0, s, B as I.Decl (_, S.Parameter NONE), collect) *)


	  (* skip'' (K, (G, B)) = K'
	   
	     Invariant:
	     If   G = x1:V1 .. xn:Vn 
	     and  G |- B = <param> ... <param> tags
	     then  K' = K, BV (x1) .. BV (xn)
	  *)

	  fun skip'' (K, (I.Null, I.Null)) = K
	    | skip'' (K, (I.Decl (G0, D), I.Decl(B0, T))) = I.Decl (skip'' (K, (G0, B0)), BV (D, T))


(* ------ *)

          val collect2 = collectGlobalSub (G0, s, B, fn (_, K') => K')
	  val collect0 = collectSub' (I.Null, t, B0, fn (_, K') => K')     (*BUG collectSub' doesn't work *)
	  val K0 = collect0 (0, I.Null)
	  val K1 = skip'' (K0, (G0, B0))
	  val K = collect2 (I.ctxLength G0, K1)

(*	  val (_, K) = collectSub' (*change later *) (G0, s, B, fn (_, K') => K')
*)
	in
	  (abstractCtx K, abstractGlobalSub (K, s, B))
	end 
*)
(*


    (* abstractNew ((G0, B0), s, B) = ((G', B'), s')

       Invariant: 
       If   . |- G0 ctx
       and  G0 |- B0 tags
       and  G0 |- s : G
       and  G |- B tags
       then . |- G' = G1, Gp, G2
       and  G' |- B' tags
       and  G' |- s' : G
    *)
    fun abstractNew ((G0, B0), s, B) =
        let



(*

	  (* collectSub (s, B) = (d', K')
	   
	     Invariant:
	     G1, G2 |- s : G 
  	     |- G1 : ctx (only context blocks)
	     |- G2 : ctx (only context blocks)
	     G |- B tags
	     then d' = |G1|
	     and  K' is a auxiliary EVar context
	    *)
	  fun collectSub' (I.Null, I.Shift 0, _, collect) = (0, collect (0, I.Null))
            | collectSub' (G0, s, B as I.Decl (_, S.Parameter (SOME l)), collect) = 
	      let
		val F.LabelDec (name, _, G2) = F.labelLookup l
		val (d, K) = skip (G0, List.length G2, s, B)
	      in
		(d, collect (d, K))
	      end
	    | collectSub' (G0, I.Dot (I.Exp (U), s), I.Decl (B, T), collect) =
	        collectSub' (G0, s, B, fn (d', K') => 
			     let 
			       val K'' = collect (d', K')
			     in
			       collectExp (T, d', G0, (U, I.id), K'')
			     end)
	    (* no cases for (G0, s, B as I.Decl (_, S.Parameter NONE), collect) *)




	  and skip (G0, 0, s, B) = collectSub' (G0, s, B, fn (_, K') => K')
	    | skip (I.Decl (G0, D), n, s, I.Decl (B, T as S.Parameter _)) =
	      let 
		val (d, K) = skip (G0, n-1, I.invDot1 s, B)
	      in
	        (d + 1, I.Decl (K, BV (D, T)))
	      end

	  val (_, K) = collectSub' (G0, s, B, fn (_, K') => K')
 
	  val _ = TextIO.print ("OK: " ^ (Int.toString (I.ctxLength K)) ^ "\n")
 ------ *)


	  val cf = collectGlobalSub (G0, s, B, fn (_, K') => K')
	  val K = cf (0, I.Null)
	in
	  (abstractCtx K, abstractGlobalSub (K, s))
	end 
*)

  in
    val weaken = weaken
    val raiseType = raiseType

    val abstractSub = abstractSubAll
    val abstractSub' = abstractNew
  end

end;  (* functor MTPAbstract *)
