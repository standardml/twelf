(* Meta Recursion Version 1.3 *)
(* Author: Carsten Schuermann *)
(* See [Rohwedder,Pfenning ESOP'96] *)

functor MTPRecursion (structure Global : GLOBAL
		      structure IntSyn : INTSYN
		      structure FunSyn : FUNSYN
			sharing FunSyn.IntSyn = IntSyn
		      structure StateSyn' : STATESYN
			sharing StateSyn'.IntSyn = IntSyn
			sharing StateSyn'.FunSyn = FunSyn
		      structure Abstract : ABSTRACT
			sharing Abstract.IntSyn = IntSyn
		      structure Whnf : WHNF
		        sharing Whnf.IntSyn = IntSyn
		      structure Unify : UNIFY
		        sharing Unify.IntSyn = IntSyn
		      structure Conv : CONV
		        sharing Conv.IntSyn = IntSyn
		      structure Trail : TRAIL
		        sharing Trail.IntSyn = IntSyn
		      structure Names : NAMES
		        sharing Names.IntSyn = IntSyn
		      structure Subordinate : SUBORDINATE
		        sharing Subordinate.IntSyn = IntSyn
		      structure Print : PRINT
		        sharing Print.IntSyn = IntSyn
		      structure FunPrint :FUNPRINT
			sharing FunPrint.FunSyn = FunSyn
		      structure Formatter : FORMATTER)  : MTPRECURSION =
struct

  structure StateSyn = StateSyn'

  exception Error of string

  type operator = StateSyn.State

  local
    structure I = IntSyn
    structure F = FunSyn
    structure S = StateSyn
    structure N = Names
    structure Fmt = Formatter


(*    datatype Quantifier =                     (* Quantifier to mark parameters *)
      Universal                               (* Q ::= Uni                     *)
    | Existential                             (*     | Ex                      *)
*)
    (* If Q marks all parameters in a context G we write   G : Q               *)


    (* duplicate code? -fp *)
(*    fun vectorToString (G, O) =
	let
	  fun fmtOrder (Order.Arg (Us, Vs)) =
	      [Fmt.String (Print.expToString (G, I.EClo Us)), Fmt.String ":",   
	       Fmt.String (Print.expToString (G, I.EClo Vs))]
	    | fmtOrder (Order.Lex L) = [Fmt.String "{", Fmt.HVbox (fmtOrders L), Fmt.String "}"]
	    | fmtOrder (Order.Simul L) = [Fmt.String "[", Fmt.HVbox (fmtOrders L), Fmt.String "]"]

	  and fmtOrders nil = nil
	    | fmtOrders (O :: nil) = fmtOrder O
	    | fmtOrders (O :: L) = fmtOrder O @ (Fmt.String " " :: fmtOrders L)
	in
	  Fmt.makestring_fmt (Fmt.HVbox (fmtOrder O))
	end
*)
    (* vector (c, (S, s)) = P'
       
       Invariant:
       If   . |- c : V   G |- s : G'    G' |- S : V > type
       and  V = {x1:V1} ... {xn:Vn} type
       and  G |- S[s] = U1 .. Un : V[s] > type
       and  sel (c) = i1 .. im
       then P' = (U1'[s1']: V1'[t1'], .., U1'[sm']: V1'[tm'])
       and  G |- sj' : Gj'    Gj' |- Uj' : V1j'
       and  G |- tj' : Gj'    Gj' |- Vj' : L
       and  G |- Vj' [tj'] = V1j' [sj'] : L
       and  G |- Uik = Uk'[sk']
    *)
(*    fun vector (c, (S, s)) =
	let 
	  val Vid = (I.constType c, I.id)
	  fun select' (n, (Ss', Vs'')) =
		select'W (n, (Ss', Whnf.whnf Vs''))
	  and select'W (1, ((I.App (U', S'), s'), (I.Pi ((I.Dec (_, V''), _), _), s''))) = 
		((U', s'), (V'', s''))
	      (* select'W (1, _, (I.Root _, _)) cannot occur by invariant ! *)
	    | select'W (n, ((I.SClo (S', s1'), s2'), Vs'')) =
		select'W (n, ((S', I.comp (s1', s2')), Vs''))
	    | select'W (n, ((I.App (U', S'), s'), (I.Pi ((I.Dec (_, V1''), _), V2''), s''))) = 
		select' (n-1, ((S', s'), (V2'', I.Dot (I.Exp (I.EClo (U', s')), s''))))
	  fun select (O.Arg n) = O.Arg (select' (n, ((S, s), Vid)))
	    | select (O.Lex L) = O.Lex (map select L)
	    | select (O.Simul L) = O.Simul (map select L)
	in
	  select (O.selLookup c)
	end      
*)
    (* set_parameter (G, X, k, sc, S) = S'

       Invariant:
       appends a list of recursion operators to S after
       instantiating X with all possible local parameters (between 1 and k)
    *)
    fun set_parameter (G, X as I.EVar (r, _, V, _), k, sc, S) =
	let 
	  fun set_parameter' (0, S') =  S'
	    | set_parameter' (k', S') = 
		let 
		  val D' as I.Dec (_, V') = I.ctxDec (G, k')
		  val S'' = 
		    Trail.trail (fn () => 
				 if Unify.unifiable (G, (V, I.id), (V', I.id))
				   andalso Unify.unifiable (G, (X, I.id), (I.Root (I.BVar k', I.Nil), I.id))
				   then sc S'
				 else S')
		in 
		  set_parameter' (k'-1, S'')
		end
	in
	  set_parameter' (k, S)
	end

    (* ltinit (G, k, ((U1, s1), (V2, s2)), ((U3, s3), (V4, s4)), sc, S) = S'
     
       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1
       and  G |- s2 : G2   G2 |- V2 : L
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  S is a set of all all possible states
       and  sc is success continuation
       then S' is an extension of S, containing all 
	    recursion operators
    *)
    fun ltinit (G, k, (Us, Vs), UsVs', sc, S) = 
          ltinitW (G, k, Whnf.whnfEta (Us, Vs), UsVs', sc, S)
    and ltinitW (G, k, (Us, Vs as (I.Root _, _)), UsVs', sc, S) =
          lt (G, k, (Us, Vs), UsVs', sc, S)
      | ltinitW (G, k, 
		 ((I.Lam (D1, U), s1), (I.Pi (D2, V), s2)), 
		 ((U', s1'), (V', s2')),
		 sc, S) =
          ltinit (I.Decl (G, I.decSub (D1, s1) (* = I.decSub (D2, s2) *)), k+1, 
		  ((U, I.dot1 s1), (V, I.dot1 s2)), 
		  ((U', I.comp (s1', I.shift)), (V', I.comp (s2', I.shift))), 
		  sc, S)

    (* lt (G, k, ((U, s1), (V, s2)), (U', s'), sc, S) = S'
     
       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  k is the length of the local context
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  S is a set of already calculuate possible states
       and  sc is success continuation
       then S' is an extension of S, containing all 
	    recursion operators
    *)

    (* Vs is Root!!! *)
    (* (Us',Vs') may not be eta-expanded!!! *)
    and lt (G, k, (Us, Vs), (Us', Vs'), sc, S) = 
          ltW (G, k, (Us, Vs), Whnf.whnfEta (Us', Vs'), sc, S)
    and ltW (G, k, (Us, Vs), ((I.Root (I.Const c, S'), s'), Vs'), sc, St) = 
	  ltSpine (G, k, (Us, Vs), ((S', s'), (I.constType c, I.id)), sc, St)
      | ltW (G, k, (Us, Vs), ((I.Root (I.BVar n, S'), s'), Vs'), sc, St) = 
	  if n <= k then  (* n must be a local variable *)
	    let 
	      val I.Dec (_, V') = I.ctxDec (G, n)
	    in
	      ltSpine (G, k, (Us, Vs), ((S', s'), (V', I.id)), sc, St)
	    end
	  else St
      | ltW (G, _, _, ((I.EVar _, _), _), _, S) = S
      | ltW (G, k, ((U, s1), (V, s2)), ((I.Lam (D as I.Dec (_, V1'), U'), s1'), 
					(I.Pi ((I.Dec (_, V2'), _), V'), s2')), sc, S) =
	if Subordinate.equiv (I.targetFam V, I.targetFam V1') (* == I.targetFam V2' *) then 
	  let  (* enforce that X gets only bound to parameters *) 
	    val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	    val sc' = fn S' => set_parameter (G, X, k, sc, S')
	  in
	    lt (G, k, ((U, s1), (V, s2)), 
		((U', I.Dot (I.Exp (X), s1')), 
		 (V', I.Dot (I.Exp (X), s2'))), sc', S)
	  end
	else
	  if Subordinate.below (I.targetFam V1', I.targetFam V) then
	    let 
	      val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	    in
	      lt (G, k, ((U, s1), (V, s2)), 
		  ((U', I.Dot (I.Exp (X), s1')), 
		   (V', I.Dot (I.Exp (X), s2'))), sc, S)
	    end
	  else S

    and ltSpine (G, k, (Us, Vs), (Ss', Vs'), sc, S) = 
          ltSpineW (G, k, (Us, Vs), (Ss', Whnf.whnf Vs'), sc, S) 
    and ltSpineW (G, k, (Us, Vs), ((I.Nil, _), _), _, S) = S
      | ltSpineW (G, k, (Us, Vs), ((I.SClo (S, s'), s''), Vs'), sc, St) =
          ltSpineW (G, k, (Us, Vs), ((S, I.comp (s', s'')), Vs'), sc, St)
      | ltSpineW (G, k, (Us, Vs), ((I.App (U', S'), s1'), 
				   (I.Pi ((I.Dec (_, V1'), _), V2'), s2')), sc, St) = 
	let
	  val St' = le (G, k, (Us, Vs), ((U', s1'), (V1', s2')), sc, St)
	in
	  ltSpine (G, k, (Us, Vs), ((S', s1'), 
				 (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))), sc, St')
	end

    (* eq (G, ((U, s1), (V, s2)), (U', s'), sc, S) = S'
     
       Invariant:
       If   G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  S is a set of already calculuated possible states
       and  sc is success continuation
       then S' is an extension of S, containing all 
	    recursion operators resulting from U[s1] = U'[s']
    *)
    and eq (G, (Us, Vs), (Us', Vs'), sc, S) = 
        (Trail.trail (fn () => 
		      if Unify.unifiable (G, Vs, Vs') 
			andalso Unify.unifiable (G, Us, Us') 
			then sc S
		      else S))
    

    (* le (G, k, ((U, s1), (V, s2)), (U', s'), sc, S) = S'
     
       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  k is the length of the local context
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  S is a set of already calculuated possible states
       and  sc is success continuation
       then S' is an extension of S, containing all 
	    recursion operators resulting from U[s1] <= U'[s']
    *)

    and le (G, k, (Us, Vs), (Us', Vs'), sc, S) = 
	let 
	  val S' = eq (G, (Us, Vs), (Us', Vs'), sc, S)
	in
	  leW (G, k, (Us, Vs), Whnf.whnfEta (Us', Vs'), sc, S')
	end

    and leW (G, k, ((U, s1), (V, s2)), ((I.Lam (D as I.Dec (_, V1'), U'), s1'), 
					(I.Pi ((I.Dec (_, V2'), _), V'), s2')), sc, S) =
	if Subordinate.equiv (I.targetFam V, I.targetFam V1') (* == I.targetFam V2' *) then 
	  let
	    val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	    val sc' = fn S' => set_parameter (G, X, k, sc, S')
	  (* enforces that X can only bound to parameter *)
	  in                         
	    le (G, k, ((U, s1), (V, s2)), 
		((U', I.Dot (I.Exp (X), s1')), 
		 (V', I.Dot (I.Exp (X), s2'))), sc', S)
	  end
	else
	  if Subordinate.below  (I.targetFam V1', I.targetFam V) then
	    let 
	      val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	    in
	      le (G, k, ((U, s1), (V, s2)), 
		  ((U', I.Dot (I.Exp (X), s1')), 
		   (V', I.Dot (I.Exp (X), s2'))), sc, S)
	    end
	  else S
      | leW (G, k, (Us, Vs), (Us', Vs'), sc, S) = lt (G, k, (Us, Vs), (Us', Vs'), sc, S) 

	      
    (* ordlt (G, O1, O2, sc, S) = S'
     
       Invariant:
       If   G |- O1 augmented subterms   
       and  G |- O2 augmented subterms
       and  S is a set of already calculuated possible states
       and  sc is success continuation
       then S' is an extension of S, containing all 
	    recursion operators of all instantiations of EVars s.t. O1 is
	    lexicographically smaller than O2
    *)
    fun ordlt (G, S.Arg UsVs, S.Arg UsVs', sc, S) =  ltinit (G, 0, UsVs, UsVs', sc, S)
      | ordlt (G, S.Lex L, S.Lex L', sc, S) = ordltLex (G, L, L', sc, S)
      | ordlt (G, S.Simul L, S.Simul L', sc, S) = ordltSimul (G, L, L', sc, S)


    (* ordltLex (G, L1, L2, sc, S) = S'
     
       Invariant:
       If   G |- L1 list of augmented subterms   
       and  G |- L2 list of augmented subterms
       and  S is a set of already calculuated possible states
       and  sc is success continuation
       then S' is an extension of S, containing all 
	    recursion operators of all instantiations of EVars s.t. L1 is
	    lexicographically less then L2
    *)
    and ordltLex (G, nil, nil, sc, S) = S
      | ordltLex (G, O :: L, O' :: L', sc, S) =
        let 
	  val S' = Trail.trail (fn () => ordlt (G, O, O', sc, S))
	in 
	  ordeq (G, O, O', fn S'' =>  ordltLex (G, L, L', sc, S''), S')
	end

    (* ordltSimul (G, L1, L2, sc, S) = S'
     
       Invariant:
       If   G |- L1 list of augmented subterms   
       and  G |- L2 list of augmented subterms
       and  S is a set of already calculuated possible states
       and  sc is success continuation
       then S' is an extension of S, containing all 
	    recursion operators of all instantiations of EVars s.t. L1 is
	    simultaneously smaller than L2
    *)
    and ordltSimul (G, nil, nil, sc, S) = S
      | ordltSimul (G, O :: L, O' :: L', sc, S) = 
        let
	  val S'' = Trail.trail (fn () => ordlt (G, O, O',
			fn S' => ordleSimul (G, L, L', sc, S'), S))
	in 
	  ordeq (G, O, O', fn S' => ordltSimul (G, L, L', sc, S'), S'')
	end

    (* ordleSimul (G, L1, L2, sc, S) = S'
     
       Invariant:
       If   G |- L1 list of augmented subterms   
       and  G |- L2 list of augmented subterms
       and  S is a set of already calculuated possible states
       and  sc is success continuation
       then S' is an extension of S, containing all 
	    recursion operators of all instantiations of EVars s.t. L1 is
	    simultaneously smaller than or equal to L2
    *)
    and ordleSimul (G, nil, nil, sc, S) = sc S
      | ordleSimul (G, O :: L, O' :: L', sc, S) =
          ordle (G, O, O', fn S' => ordleSimul (G, L, L', sc, S'), S)

	      
    (* ordeq (G, O1, O2, sc, S) = S'
     
       Invariant:
       If   G |- O1 augmented subterms   
       and  G |- O2 augmented subterms
       and  S is a set of already calculuated possible states
       and  sc is success continuation
       then S' is an extension of S, containing all 
	    recursion operators of all instantiations of EVars s.t. O1 is
	    convertible to O2
    *)
    and ordeq (G, S.Arg (Us, Vs), S.Arg (Us' ,Vs'), sc, S) =  
          if Unify.unifiable (G, Vs, Vs') andalso Unify.unifiable (G, Us, Us') then sc S else S
      | ordeq (G, S.Lex L, S.Lex L', sc, S) = ordeqs (G, L, L', sc, S)
      | ordeq (G, S.Simul L, S.Simul L', sc, S) = ordeqs (G, L, L', sc, S)
      
    (* ordlteqs (G, L1, L2, sc, S) = S'
     
       Invariant:
       If   G |- L1 list of augmented subterms   
       and  G |- L2 list of augmented subterms
       and  S is a set of already calculuated possible states
       and  sc is success continuation
       then S' is an extension of S, containing all 
	    recursion operators of all instantiations of EVars s.t. L1 is
	    convertible to L2
    *)
    and ordeqs (G, nil, nil, sc, S) = sc S
      | ordeqs (G, O :: L, O' :: L', sc, S) = 
          ordeq (G, O, O', fn S' => ordeqs (G, L, L', sc, S'), S)

    (* ordeq (G, O1, O2, sc, S) = S'
     
       Invariant:
       If   G |- O1 augmented subterms   
       and  G |- O2 augmented subterms
       and  S is a set of already calculuated possible states
       and  sc is success continuation
       then S' is an extension of S, containing all 
1	    recursion operators of all instantiations of EVars s.t. O1 is
	    convertible to O2 or smaller than O2
    *)
    and ordle (G, O, O', sc, S) = 
	let 
	  val S' = Trail.trail (fn () => ordeq (G, O, O', sc, S))
	in
	  ordlt (G, O, O', sc, S')
	end


    (* select (G, (V, s)) = (G', (V1', s1'), (V2', s2'))

     Invariant: 
     If   G |- s : G1   G1 |- V : type
     and  G |- V [s] = {V1} ... {Vn} a S
     then G' = G, V1 .. Vn 
     and  G' |- s1' : G1'   G1' |- V1' : type
     and  G' |- s2' : G2'   G2' |- V2' : type
     and  G' |- V1' [s1'] = V1 [^n]
     and  G' |- V2' [s2'] = a S
    *)
(*    fun select (G, Vs) = selectW (G, (Whnf.whnf Vs))
    and selectW (G, (I.Pi ((D as I.Dec (_, V1), _), V2), s)) =
	let 
	  fun select' (G, (Vs1, Vs2)) = 
	      selectW' (G, (Vs1, Whnf.whnf Vs2))
	  and selectW' (G, (Vs1, Vs2 as (I.Root _, _))) = (G, (Vs1, Vs2))
	    | selectW' (G, ((V1, s1), (I.Pi ((D, P), V2'), s2))) =
		select' (I.Decl (G, I.decSub (D, s2)), ((V1, I.comp (s1, I.shift)), 
							(V2', I.dot1 s2)))
	in
	  select' (I.Decl (G, I.decSub (D, s)) , ((V1, I.comp (s, I.shift)), (V2, I.dot1 s)))
	end
*)
    (* lemma (S, t, S) = (G', P', P'', abstract', S')
     
       Invariant:
       If   S state  (S = ((G, M), V)
                     |- G ctx
                     G |- M mtx
		     G |- V = {V1} ... {Vn} a S)
       and  S' state derived from S by an inductive call to t
       and  S a list of operators
       then G is context, where all - variables are replaced by EVars in S'
       and  P' is induction variable vector of EVars in the inductive call
       and  P'' is induction variable vector of the theorem S.
       and  G' |- P' : (V1' .. Vn')       
	      (where  t : {W1} ..{Wm} b S, and Vi' are among W1 .. Wm) 
       and  G'' |- P'' : (V1'' .. Vn'')
	      (where  a : {W1} ..{Wm} b S, and Vi'' are among W1 .. Wm)
	 
    *) 
(*    fun lemma (S, t, S) =
	let
	  val M.State (name, GM, V) = Lemma.apply (S, t)
	  val (M.Prefix (G', M', B'), s') = createEVars GM  
	  val (G'', ((I.Root (I.Const a1, S1), s1), 
		     (I.Root (I.Const a2, S2), s2))) = select (G', (V, s'))
	in
	  (G'', vector (a1, (S1, s1)), vector (a2, (S2, s2)), 
	   fn S' => ((MetaAbstract.abstract (M.State (name, M.Prefix (G', M', B'), 
							I.EClo (V, s')))) :: S'), S)
	end
*)
(*
    (* expandLazy' (S, L, S) = S'

       Invariant: 
       If   S state
       and  L list of mutual recursive type families
       and  S a list of operators
       then S' extends S by all operators 
	 representing inductive calls to theorems in L
    *)
    fun expandLazy' (S, O.Empty, S) = S
      | expandLazy' (S, (O.LE (t, L)), S) = expandLazy' (S, L, ordle (lemma (S, t, S)))
      | expandLazy' (S, (O.LT (t, L)), S) = expandLazy' (S, L, ordlt (lemma (S, t, S)))

      
    fun recursionDepth V =
	let 
	  fun recursionDepth' (I.Root _, n) = n 
	    | recursionDepth' (I.Pi (_, V), n) = recursionDepth' (V, n+1)
	in
	  recursionDepth' (V, 0)
	end

    (* expandLazy S = S'

       Invariant: 
       If   S State
       then S' a list of operations which cause a recursive call
         (only induction variables are instantiated)
    *)
    fun expandLazy (S as M.State (_, _, V)) =
        if recursionDepth V > (!MetaGlobal.maxRecurse) then nil
	else expandLazy' (S, (O.mutLookup (I.targetFam  V)), nil)


    (* inputConv ((V1, s1), (V2, s2)) = B

       Invariant:
       If  G |- s1 : G1   G1 |- V1 : L
       and G |- s2 : G2   G2 |- V2 : L
       and G |- V1[s1] = c1 ; S1  
       and G |- V2[s2] = c2 ; S2
       then B' holds iff c1 =  c2 and V1[s1] ==+ V2[s2]   (convertible on + arguments of c1)
    *)
    fun inputConv (Vs1, Vs2) = inputConvW (Whnf.whnf Vs1, Whnf.whnf Vs2)
    and inputConvW ((I.Root (I.Const c1, S1), s1), (I.Root (I.Const c2, S2), s2)) =
          (* s1 = s2 = id *)
          if c1 = c2 then inputConvSpine (valOf (ModeSyn.modeLookup c1), 
					  ((S1, s1), (I.constType c1, I.id)), 
					  ((S2, s2), (I.constType c2, I.id)))
	  else false
    
    and inputConvSpine (ModeSyn.Mnil, ((S1, _), _), ((S2, _), _)) = true (* S1 = S2 = Nil *)
      | inputConvSpine (mS, ((I.SClo (S1, s1'), s1), Vs1), (Ss2, Vs2)) =
          inputConvSpine (mS, ((S1, I.comp (s1', s1)), Vs1), (Ss2, Vs2))
      | inputConvSpine (mS, (Ss1, Vs1), ((I.SClo (S2, s2'), s2), Vs2)) = 
	  inputConvSpine (mS, (Ss1, Vs1), ((S2, I.comp (s2', s2)), Vs2))
      | inputConvSpine (ModeSyn.Mapp (ModeSyn.Marg (ModeSyn.Minus, _), mS), 
			((I.App (U1, S1), s1), (I.Pi ((I.Dec (_, V1), _), W1), t1)),
			((I.App (U2, S2), s2), (I.Pi ((I.Dec (_, V2), _), W2), t2))) =
	  Conv.conv ((V1, t1), (V2, t2)) andalso	  
	  inputConvSpine (mS, 
			  ((S1, s1), (W1, I.Dot (I.Exp (I.EClo (U1, s1)), t1))),
			  ((S2, s2), (W2, I.Dot (I.Exp (I.EClo (U1, s1)), t2))))
          (* BUG: use the same variable (U1, s1) to continue comparing! --cs
                  in ((S2, s2), (W2, I.Dot (I.Exp (I.EClo (U2, s2), V2), t2))))
	     FIXED: --cs Mon Nov  9 19:38:55 EST 1998 *)
	| inputConvSpine (ModeSyn.Mapp (ModeSyn.Marg (ModeSyn.Plus, _), mS),
			((I.App (U1, S1), s1), (I.Pi ((I.Dec (_, V1), _), W1), t1)),
			((I.App (U2, S2), s2), (I.Pi ((I.Dec (_, V2), _), W2), t2))) =
	   inputConvSpine (mS, 
			  ((S1, s1), (W1, I.Dot (I.Exp (I.EClo (U1, s1)), t1))),
			  ((S2, s2), (W2, I.Dot (I.Exp (I.EClo (U2, s2)), t2))))


    (* removeDuplicates S = S'

       Invariant:
       If   S is a list of recursion operators,
       then S' is a sublist of S, s.t.
	 forall S = ((G, M), V) in S' 
               |- G ctx
	       G |- M mtx
	       G |- V = {V0} .. {Vn} a ; S : type
	       and Vi = ci ; S'
	       and forall 1 <= i <= n: 
		 either ci =/= c0 orelse
		 G, V0 .. Vi |- V0 [^ i] =/=+ Vi (not convertible on + arguments on c0)
    *)
    fun removeDuplicates nil = nil
      | removeDuplicates (S' :: S) =
	let
	  fun compExp (Vs1, Vs2) = 
		compExpW (Whnf.whnf Vs1, Whnf.whnf Vs2)
	  and compExpW (Vs1, (I.Root _, _)) = false
	    | compExpW (Vs1 as (V1, s1), (I.Pi ((D2, _), V2), s2)) =
		compDec (Vs1, (D2, s2)) 
		orelse compExp ((V1, I.comp (s1, I.shift)), (V2, I.dot1 s2))

	  and compDec (Vs1, (I.Dec (_, V2), s2)) =
	        inputConv (Vs1, (V2, s2))

	  fun check (M.State (name, GM, V)) = checkW (Whnf.whnf (V, I.id))
	  and checkW (I.Pi ((D, _), V), s) =
		checkDec ((D, I.comp (s, I.shift)), (V, I.dot1 s)) 
	  and checkDec ((I.Dec (_, V1), s1), Vs2) =
		compExp ((V1, s1), Vs2)
	in
	  if check S' then removeDuplicates S
	  else S' :: (removeDuplicates S)
	end

    (* fillS S = S'
      
       Invariant:
       If   S is a list of lazy recursion operators
       then S' is a list of recursion operators combined with a filling
	 operator to fill non-index variables.
    *)
    fun fillS nil = nil
      | fillS (S' :: S) =
	let 
	  fun fillS' nil = nil
	    | fillS' (O :: _) = (Filling.apply O)

	  val (fillop, _) = Filling.expand S'
	in
	  (fillS' fillop) @ (fillS S)
	end

*)

    fun check (s, O) S = 
(* Check for duplicates,
   generate new assumption,
   residual goals *)
      (if Abstract.closedSub (I.Null, s) then TextIO.print ("IH <A> found\n")
       else TextIO.print ("IH <R> found\n");S)


    fun calc (n', G', (F', s'), (O', t'), S as S.State (n, (G, B), (IH, OH), d, O, H, F)) =
	let
	  val Ot' = S.orderSub (O', t')
	in 
	  if n < n' then ordle (G, Ot', O, check (t', Ot'), S)
	  else ordlt (G, Ot', O, check (t', Ot'), S)
	end

    (* createEVars (n, G, (F, s), (O, t), S) = S'
      
       Invariant:
       If   G |- s : G1  and  G1 |- F formula
       and  G |- t : G2  and  G2 |- O order
       and  S is a state
       then S' is the state with 
       sc returns with all addition assumptions/residual lemmas for a certain
       branch of the theorem.
    *)
    fun createEVars (n, G, (F.All (F.Prim (D as I.Dec (_, V)), F), s), (S.All (_, O), t), S) =
        let 
	  val X = I.newEVar (G, I.EClo (V, s))
	in
	  createEVars (n, G, (F, I.Dot (I.Exp X, s)), (O, I.Dot (I.Exp X, t)), S)
	end
      | createEVars (n, G, (F.And (F1, F2), s), (S.And (O1, O2), t), S) =
	let
	  val (n', S') = createEVars (n, G, (F1, s), (O1, t), S)
	in
	  createEVars (n, G, (F2, s), (O2, t), S')
	end
      | createEVars (n, G, (F.TClo (F, s'), s), (O, t), S) =
	  createEVars (n, G, (F, I.comp (s', s)), (O, t), S)
      | createEVars (n, G, (F, s), (O, t), S) = (n+1, calc (n, G, (F, s), (O, t), S))


    fun expand (S as S.State (n, (G, B), (IH, OH), d, O, H, F)) =
      let 
	val s = I.Shift (I.ctxLength G)
	val (_, S') = createEVars (1, G, (IH, s), (OH, s), S)
      in
	S'
      end



    (* expandEager S = S'

       Invariant: 
       If   S State
       then S' a list of operations which cause a recursive call
         (all variables of recursive call are instantiated)
    *)
(*    fun expandEager S = removeDuplicates (fillOp"s" (expandLazy S)) *)
    

    fun apply S = S

    fun menu _ = "Recursion : " 

    fun handleExceptions f P = 
        (f P) handle Order.Error s => raise Error s

  in
    val expand = handleExceptions expand
    val apply = apply
    val menu = menu 
  end (* local *)
end; (* functor MTPRecursion *)
