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
		      structure FunTypeCheck : FUNTYPECHECK
			sharing FunTypeCheck.FunSyn = FunSyn
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
		      structure TypeCheck : TYPECHECK
			sharing TypeCheck.IntSyn = IntSyn
		      structure Formatter : FORMATTER
		      structure FunPrint :FUNPRINT
			sharing FunPrint.FunSyn = FunSyn
			sharing FunPrint.Formatter = Formatter)  : MTPRECURSION =
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

    datatype Dec =			(* Newly created *)
      Ass of int * S.Order * I.dctx	(* Induction hypothesis  *)
    | Lemma of int * F.For		(* Residual Lemma *)

    (* set_parameter (G, X, k, sc, S) = S'

       Invariant:
       appends a list of recursion operators to S after
       instantiating X with all possible local parameters (between 1 and k)
    *)
    fun set_parameter (G, X as I.EVar (r, _, V, _), k, sc, Ds) =
	let 
	  fun set_parameter' (0, Ds') =  Ds'
	    | set_parameter' (k', Ds') = 
		let 
		  val D' as I.Dec (_, V') = I.ctxDec (G, k')
		  val Ds'' = 
		    Trail.trail (fn () => 
				 if Unify.unifiable (G, (V, I.id), (V', I.id))
				   andalso Unify.unifiable (G, (X, I.id), (I.Root (I.BVar k', I.Nil), I.id))
				   then sc Ds'
				 else Ds')
		in 
		  set_parameter' (k'-1, Ds'')
		end
	in
	  set_parameter' (k, Ds)
	end

    (* ltinit (G, k, ((U1, s1), (V2, s2)), ((U3, s3), (V4, s4)), sc, Ds) = Ds'
     
       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1
       and  G |- s2 : G2   G2 |- V2 : L
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  Ds is a set of all all possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all 
	    recursion operators
    *)
    fun ltinit (G, k, (Us, Vs), UsVs', sc, Ds) = 
          ltinitW (G, k, Whnf.whnfEta (Us, Vs), UsVs', sc, Ds)
    and ltinitW (G, k, (Us, Vs as (I.Root _, _)), UsVs', sc, Ds) =
          lt (G, k, (Us, Vs), UsVs', sc, Ds)
      | ltinitW (G, k, 
		 ((I.Lam (D1, U), s1), (I.Pi (D2, V), s2)), 
		 ((U', s1'), (V', s2')),
		 sc, Ds) =
          ltinit (I.Decl (G, I.decSub (D1, s1) (* = I.decSub (D2, s2) *)), k+1, 
		  ((U, I.dot1 s1), (V, I.dot1 s2)), 
		  ((U', I.comp (s1', I.shift)), (V', I.comp (s2', I.shift))), 
		  sc, Ds)

    (* lt (G, k, ((U, s1), (V, s2)), (U', s'), sc, Ds) = Ds'
     
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
       and  Ds is a set of already calculuate possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all 
	    recursion operators
    *)

    (* Vs is Root!!! *)
    (* (Us',Vs') may not be eta-expanded!!! *)
    and lt (G, k, (Us, Vs), (Us', Vs'), sc, Ds) = 
          ltW (G, k, (Us, Vs), Whnf.whnfEta (Us', Vs'), sc, Ds)
    and ltW (G, k, (Us, Vs), ((I.Root (I.Const c, S'), s'), Vs'), sc, Ds) = 
	  ltSpine (G, k, (Us, Vs), ((S', s'), (I.constType c, I.id)), sc, Ds)
      | ltW (G, k, (Us, Vs), ((I.Root (I.BVar n, S'), s'), Vs'), sc, Ds) = 
	  if n <= k then  (* n must be a local variable *)
	    let 
	      val I.Dec (_, V') = I.ctxDec (G, n)
	    in
	      ltSpine (G, k, (Us, Vs), ((S', s'), (V', I.id)), sc, Ds)
	    end
	  else Ds
      | ltW (G, _, _, ((I.EVar _, _), _), _, Ds) = Ds
      | ltW (G, k, ((U, s1), (V, s2)), ((I.Lam (D as I.Dec (_, V1'), U'), s1'), 
					(I.Pi ((I.Dec (_, V2'), _), V'), s2')), sc, Ds) =
	if Subordinate.equiv (I.targetFam V, I.targetFam V1') (* == I.targetFam V2' *) then 
	  let  (* enforce that X gets only bound to parameters *) 
	    val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	    val sc' = fn Ds' => set_parameter (G, X, k, sc, Ds')
	  in
	    lt (G, k, ((U, s1), (V, s2)), 
		((U', I.Dot (I.Exp (X), s1')), 
		 (V', I.Dot (I.Exp (X), s2'))), sc', Ds)
	  end
	else
	  if Subordinate.below (I.targetFam V1', I.targetFam V) then
	    let 
	      val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	    in
	      lt (G, k, ((U, s1), (V, s2)), 
		  ((U', I.Dot (I.Exp (X), s1')), 
		   (V', I.Dot (I.Exp (X), s2'))), sc, Ds)
	    end
	  else Ds

    and ltSpine (G, k, (Us, Vs), (Ss', Vs'), sc, Ds) = 
          ltSpineW (G, k, (Us, Vs), (Ss', Whnf.whnf Vs'), sc, Ds) 
    and ltSpineW (G, k, (Us, Vs), ((I.Nil, _), _), _, Ds) = Ds
      | ltSpineW (G, k, (Us, Vs), ((I.SClo (S, s'), s''), Vs'), sc, Ds) =
          ltSpineW (G, k, (Us, Vs), ((S, I.comp (s', s'')), Vs'), sc, Ds)
      | ltSpineW (G, k, (Us, Vs), ((I.App (U', S'), s1'), 
				   (I.Pi ((I.Dec (_, V1'), _), V2'), s2')), sc, Ds) = 
	let
	  val Ds' = le (G, k, (Us, Vs), ((U', s1'), (V1', s2')), sc, Ds)
	in
	  ltSpine (G, k, (Us, Vs), ((S', s1'), 
				 (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))), sc, Ds')
	end

    (* eq (G, ((U, s1), (V, s2)), (U', s'), sc, Ds) = Ds'
     
       Invariant:
       If   G |- s1 : G1   G1 |- U1 : V1   (U1 [s1] in  whnf)
       and  G |- s2 : G2   G2 |- V2 : L    (V2 [s2] in  whnf)
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all 
	    recursion operators resulting from U[s1] = U'[s']
    *)
    and eq (G, (Us, Vs), (Us', Vs'), sc, Ds) = 
        (Trail.trail (fn () => 
		      if Unify.unifiable (G, Vs, Vs') 
			andalso Unify.unifiable (G, Us, Us') 
			then sc Ds
		      else Ds))
    

    (* le (G, k, ((U, s1), (V, s2)), (U', s'), sc, Ds) = Ds'
     
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
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all 
	    recursion operators resulting from U[s1] <= U'[s']
    *)

    and le (G, k, (Us, Vs), (Us', Vs'), sc, Ds) = 
	let 
	  val Ds' = eq (G, (Us, Vs), (Us', Vs'), sc, Ds)
	in
	  leW (G, k, (Us, Vs), Whnf.whnfEta (Us', Vs'), sc, Ds')
	end

    and leW (G, k, ((U, s1), (V, s2)), ((I.Lam (D as I.Dec (_, V1'), U'), s1'), 
					(I.Pi ((I.Dec (_, V2'), _), V'), s2')), sc, Ds) =
	if Subordinate.equiv (I.targetFam V, I.targetFam V1') (* == I.targetFam V2' *) then 
	  let
	    val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	    val sc' = fn Ds' => set_parameter (G, X, k, sc, Ds')
	  (* enforces that X can only bound to parameter *)
	  in                         
	    le (G, k, ((U, s1), (V, s2)), 
		((U', I.Dot (I.Exp (X), s1')), 
		 (V', I.Dot (I.Exp (X), s2'))), sc', Ds)
	  end
	else
	  if Subordinate.below  (I.targetFam V1', I.targetFam V) then
	    let 
	      val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	    in
	      le (G, k, ((U, s1), (V, s2)), 
		  ((U', I.Dot (I.Exp (X), s1')), 
		   (V', I.Dot (I.Exp (X), s2'))), sc, Ds)
	    end
	  else Ds
      | leW (G, k, (Us, Vs), (Us', Vs'), sc, Ds) = lt (G, k, (Us, Vs), (Us', Vs'), sc, Ds) 

	      
    (* ordlt (G, O1, O2, sc, Ds) = Ds'
     
       Invariant:
       If   G |- O1 augmented subterms   
       and  G |- O2 augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all 
	    recursion operators of all instantiations of EVars s.t. O1 is
	    lexicographically smaller than O2
    *)
    fun ordlt (G, S.Arg UsVs, S.Arg UsVs', sc, Ds) =  ltinit (G, 0, UsVs, UsVs', sc, Ds)
      | ordlt (G, S.Lex L, S.Lex L', sc, Ds) = ordltLex (G, L, L', sc, Ds)
      | ordlt (G, S.Simul L, S.Simul L', sc, Ds) = ordltSimul (G, L, L', sc, Ds)


    (* ordltLex (G, L1, L2, sc, Ds) = Ds'
     
       Invariant:
       If   G |- L1 list of augmented subterms   
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all 
	    recursion operators of all instantiations of EVars s.t. L1 is
	    lexicographically less then L2
    *)
    and ordltLex (G, nil, nil, sc, Ds) = Ds
      | ordltLex (G, O :: L, O' :: L', sc, Ds) =
        let 
	  val Ds' = Trail.trail (fn () => ordlt (G, O, O', sc, Ds))
	in 
	  ordeq (G, O, O', fn Ds'' =>  ordltLex (G, L, L', sc, Ds''), Ds')
	end

    (* ordltSimul (G, L1, L2, sc, Ds) = Ds'
     
       Invariant:
       If   G |- L1 list of augmented subterms   
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all 
	    recursion operators of all instantiations of EVars s.t. L1 is
	    simultaneously smaller than L2
    *)
    and ordltSimul (G, nil, nil, sc, Ds) = Ds
      | ordltSimul (G, O :: L, O' :: L', sc, Ds) = 
        let
	  val Ds'' = Trail.trail (fn () => ordlt (G, O, O',
			fn Ds' => ordleSimul (G, L, L', sc, Ds'), Ds))
	in 
	  ordeq (G, O, O', fn Ds' => ordltSimul (G, L, L', sc, Ds'), Ds'')
	end

    (* ordleSimul (G, L1, L2, sc, Ds) = Ds'
     
       Invariant:
       If   G |- L1 list of augmented subterms   
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all 
	    recursion operators of all instantiations of EVars s.t. L1 is
	    simultaneously smaller than or equal to L2
    *)
    and ordleSimul (G, nil, nil, sc, Ds) = sc Ds
      | ordleSimul (G, O :: L, O' :: L', sc, Ds) =
          ordle (G, O, O', fn Ds' => ordleSimul (G, L, L', sc, Ds'), Ds)

	      
    (* ordeq (G, O1, O2, sc, Ds) = Ds'
     
       Invariant:
       If   G |- O1 augmented subterms   
       and  G |- O2 augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all 
	    recursion operators of all instantiations of EVars s.t. O1 is
	    convertible to O2
    *)
    and ordeq (G, S.Arg (Us, Vs), S.Arg (Us' ,Vs'), sc, Ds) =  
          if Unify.unifiable (G, Vs, Vs') andalso Unify.unifiable (G, Us, Us') then sc Ds else Ds
      | ordeq (G, S.Lex L, S.Lex L', sc, Ds) = ordeqs (G, L, L', sc, Ds)
      | ordeq (G, S.Simul L, S.Simul L', sc, Ds) = ordeqs (G, L, L', sc, Ds)
      
    (* ordlteqs (G, L1, L2, sc, Ds) = Ds'
     
       Invariant:
       If   G |- L1 list of augmented subterms   
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all 
	    recursion operators of all instantiations of EVars s.t. L1 is
	    convertible to L2
    *)
    and ordeqs (G, nil, nil, sc, Ds) = sc Ds
      | ordeqs (G, O :: L, O' :: L', sc, Ds) = 
          ordeq (G, O, O', fn Ds' => ordeqs (G, L, L', sc, Ds'), Ds)

    (* ordeq (G, O1, O2, sc, Ds) = Ds'
     
       Invariant:
       If   G |- O1 augmented subterms   
       and  G |- O2 augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all 
1	    recursion operators of all instantiations of EVars s.t. O1 is
	    convertible to O2 or smaller than O2
    *)
    and ordle (G, O, O', sc, Ds) = 
	let 
	  val Ds' = Trail.trail (fn () => ordeq (G, O, O', sc, Ds))
	in
	  ordlt (G, O, O', sc, Ds')
	end

    (* residualLemma (s, F) = F'
     
       Invariant:
       If   G |- s : Gx    and  . |- F = {{Gx}} F1 formula
       and  Gx |- F1 == [[Gy]] true
       then G |- {{Gx'}} F' formula
       where Gx' < Gx
       and   s uninstantiated on Gx'
    *)

    fun residualLemma (G, Gx, (Fx, s)) =
      let 
	(* collect (G, s, F) = (Gx', F')
	 
	   Invariant: 
	   If   G |- s : Gx    and  . |- F = {{Gx}} F1 formula
	   then G |- Gx' ctx
	   and  Gx' < Gx  (where s uninstantiated on Gx')
	   and  G, Gx' |- F' formula
	   and  G, Gx' |- F' = [[Gy]] true
	*)
	  
	fun collect (s as I.Shift k, I.Null) = (I.Null, s)
	  | collect (s as I.Dot (I.Exp U, s'), I.Decl (G, D)) =
 	    let
	      val (Gx', s'') = collect (s', G)
	    in 
	      if Abstract.closedExp (G, (U, I.id)) then
		(Gx', I.Dot (I.Exp (Whnf.normalize (U, I.Shift (I.ctxLength Gx'))), s''))
	      else
		(I.Decl (Gx', I.decSub (D, s'')), I.dot1 s'')
	    end
	  
 	(* abstract (Gx, F) = F'

	   Invariant: 
	   F' = {{Gx}} F
	*)
	fun abstract (I.Null, F) = F
	  | abstract (I.Decl (Gx, D), F) = abstract (Gx, F.All (F.Prim D, F))
	  
	val (Gx', s') = collect (s, Gx)
	val F' = abstract (Gx', F.forSub (Fx, s'))
      in
	F'
      end



    fun makeCtx (G, (F.True, s)) = G
      | makeCtx (G, (F.Ex (D, F), s)) =
          makeCtx (I.Decl (G, Whnf.normalizeDec (D, s)), (F, I.dot1 s))
      

    fun nameCtx I.Null = I.Null
      | nameCtx (I.Decl (G, D)) = 
        let 
	  val G' = nameCtx G
	in
	  I.Decl (G', Names.decName (G', D))
	end


    (* Invariant: 
       Fs = (F, s),  G |- 
*)       

    fun check (G, n, s, G0, O, IH, H, Fs) Ds = 
      let
	val Frl = residualLemma (G, G0, Fs)
	val _ = if !Global.doubleCheck then FunTypeCheck.isFor (G, Frl) else ()
      in 
	if List.exists (fn (n', F') => (n = n' andalso F.convFor ((F', I.id), (Frl, I.id)))) H then
	  Ds
	else
	  Lemma (n, Frl) :: Ds
      end

    fun merge (GB, (I.Null, s), T) = (GB, I.id)
      | merge ((G, B), (I.Decl (G', D), s), T) = 
          let 
	    val ((G', B'), s') = merge ((G, B), (G', s), T)
	  in
	    ((I.Decl (G', Names.decName (G', Whnf.normalizeDec (D, I.comp(s, s')))), 
	      I.Decl (B', T)), I.comp (s', I.shift))
	  end

    fun spine 0 = I.Nil 
      | spine n = I.App (I.Root (I.BVar n, I.Nil),  spine (n-1))


    (* skolem (n, (du, de), GB, w, F, sc) = (GB', s')

       Invariant:
       If   GB, Ds |- w : GB
       and  GB, G |- F formula
       and  du = #universal quantifiers in F
       and  de = #existential quantifiers in F 
       and  sc is a continuation which
	    for all GB, Ds |- s' : GB
	    returns s''  of type  GB, Ds, G'[...] |- w'' : GB, G
	    and     V''  mapping (GB, Ds, G'[...] |- V) to (GB, Ds |- {G'[...]} V type)
	    and     F''  mapping (GB, Ds, G'[...] |- F) to (GB, Ds |- {{G'[...]}} F formula)
       then GB' = GB, Ds'    
       and  |Ds'| = de
       and  each declaration in Ds' corresponds to one existential quantifier in F
       and  GB' |- s' : GB 
    *)
    
    fun skolem ((du, de), GB, w, F.True, sc) = (GB, w)
      | skolem ((du, de), GB, w, F.All (F.Prim D, F), sc) =
          skolem ((du+1, de), GB, w, F, 
		  fn (s, de') =>	
					(* s'  :  GB, Ds |- s : GB   *)
		     let 
		       val (s', V', F') = sc (s, de')                                         
					(* s'  : GB, Ds, G'[...] |- s' : GB, G *)
					(* V'  : maps (GB, Ds, G'[...] |- V type) to (GB, Ds |- {G'[...]} V type) *)
					(* F'  : maps (GB, Ds, G'[...] |- F for) to (GB, Ds |- {{G'[...]}} F for) *)
		     in
		       (I.dot1 s', 
					(* _   : GB, Ds, G'[...], D[?] |- _ : GB, G, D *)
 			fn V => V' (I.Pi ((I.decSub (D, s'), I.Virtual), V)),  
					(* _   : maps (GB, Ds, G'[....], D[?] |- V : type) to  (GB, Ds, |- {G[....], D[?]} V : type) *)
			fn F => F' (F.All (F.Prim (I.decSub (D, s')), F))
					(* _   : maps (GB, Ds, G'[....], D[?] |- F : for) to  (GB, Ds, |- {{G[....], D[?]}} F : for) *)
			)
		     end)
      | skolem ((du, de), (G, B), w, F.Ex (I.Dec (name, V), F), sc) = 
					(* V   : GB, G |- V type *)
	  let 
	    val (s', V', F') = sc (w, de)  
					(* s'  : GB, Ds, G'[...] |- s' : GB, G *)
					(* V'  : maps  (GB, Ds, G'[...] |- V : type)   to   (GB, Ds |- {G'[...]} V : type) *)
					(* F'  : maps  (GB, Ds, G'[...] |- F : for)    to   (GB, Ds |- {{G'[...]}} F : for) *)

	    val V1 = I.EClo (V, s')
	                                (* V1  : GB, Ds, G'[...] |- V1 = V [s'] : type *)
	    val V2 = Whnf.normalize (V' V1, I.id)
					(* V2  : GB, Ds |- {G'[...]} V2 : type *)

	    val F1 = F.Ex (I.Dec (name, V1), F.True) 
					(* F1  : GB, Ds, G'[...] |- F1 : for *)
	    val F2 = F' F1
					(* F2  : GB, Ds |- {{G'[...]}} F2 : for *)
	    val _ = if !Global.doubleCheck then FunTypeCheck.isFor (G, F2) else ()

	    val D2 = I.Dec (NONE, V2)
					(* D2  : GB, Ds |- D2 : type *)
	    val T2 = S.Lemma (!MTPGlobal.maxSplit, F2)
	                                (* T2  : GB, Ds |- T2 : tag *)
	  in
	    skolem ((du, de+1), (I.Decl (G, D2), I.Decl (B, T2)), I.comp (w, I.shift), F,
		    fn (s, de') => 
					(* s   : GB, Ds, D2 |- s : GB *)
		       let
			 val (s', V', F') = sc (s, de')
					(* s'  : GB, Ds, D2, G'[...] |- s' : GB, G *)
					(* V'  : maps (GB, Ds, D2, G'[...] |- V type) to (GB, Ds, D2 |- {G'[...]} V type) *)
					(* F'  : maps (GB, Ds, D2, G'[...] |- F for) to (GB, Ds, D2 |- {{G'[...]}} F for) *)

		       in
			 (I.Dot (I.Exp (I.Root (I.BVar (du + (de' - de)), spine du)), s'),
			                (* _ : GB, Ds, D2, G'[...] |- s'' : GB, G, D *)
			  V', F')
		       end)
	  end


    (* updateState (S, (Ds, s))

       Invariant:
       G context
       G' |- S state
       G |- Ds new decs
       G' |- s : G
    *)
    fun updateState (S, (nil, s)) = S
(*      | updateState (S as S.State (n, (G, B), (IH, OH), d, O, H, R, F), (Ass (n', O', G') :: L, s)) =
        let
	  val ((G'', B''), s') = merge ((G, B), (G', s), S.Induction (!MTPGlobal.maxSplit)) 
	  val s'' = I.comp (s, s')
        in
	  updateState (S.State (n, (G'', B''), (IH, OH), d, S.orderSub (O, s'), 
				(n', S.orderSub (O', s'')) :: 
				map (fn (n', O') => (n', S.orderSub (O', s'))) H, 
				map (fn (n', F') => (n', F.forSub (F', s'))) R, F.forSub (F, s')),
		       (L, s''))
	end *)
      | updateState (S as S.State (n, (G, B), (IH, OH), d, O, H, F), (Lemma (n', Frl') :: L, s)) =
        let
	  val ((G'', B''), s') = skolem ((0, 0), (G, B), I.id, F.forSub (Frl', s), 
					 fn (s', _) => (s', fn V' => V', fn F' => F')) 
	  val s'' = I.comp (s, s')
	in
	  updateState (S.State (n, (G'', B''), (IH, OH), d, S.orderSub (O, s'), 
				(n', F.forSub (Frl', s'')) :: 
				map (fn (n', F') => (n', F.forSub (F', s'))) H, F.forSub (F, s')),
		       (L, s''))
	end
      

    fun calc (n', G', (G0, F', O', s'), S as S.State (n, (G, B), (IH, OH), d, O, H, F)) =
	let
	  val Os' = S.orderSub (O', s')
	  val check' = check (G, n', s', G0, Os', IH, H, (F', s'))
	  val Ds = if n < n' then ordle (G, Os', O, check', nil)
		   else ordlt (G, Os', O, check', nil)
	in 
	  updateState (S, (Ds, I.id))
	end

    (* createEVars (n, G, (G0, F, O, s), S) = S'
      
       Invariant:
       If   G |- s : G0  and  G0 |- F formula and  G0 |- O order
       and  S is a state
       then S' is the state with 
       sc returns with all addition assumptions/residual lemmas for a certain
       branch of the theorem.
    *)
    fun createEVars (n, G, (G0, F.All (F.Prim (D as I.Dec (_, V)), F), S.All (_, O), s), S) =
        let 
	  val X = I.newEVar (G, I.EClo (V, s))
	in
	  createEVars (n, G, (I.Decl (G0, D), F, O, I.Dot (I.Exp X, s)), S)
	end
      | createEVars (n, G, (G0, F.And (F1, F2), S.And (O1, O2), s) , S) =
	let
	  val (n', S') = createEVars (n, G, (G0, F1, O1, s), S)
	in
	  createEVars (n, G, (G0, F2, O2, s), S')
	end
      | createEVars (n, G, (G0, F, O, s), S) = (n+1, calc (n, G, (G0, F, O, s), S))


    fun expand (S as S.State (n, (G, B), (IH, OH), d, O, H, F)) =
      let 
	val s = I.Shift (I.ctxLength G)
	val (_, S') = createEVars (1, G, (I.Null, IH, OH, s), S)
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

    fun menu _ = "Recursion (calculates ALL new assumptions & residual lemmas)" 

    fun handleExceptions f P = 
        (f P) handle Order.Error s => raise Error s

  in
    val expand = handleExceptions expand
    val apply = apply
    val menu = menu 
  end (* local *)
end; (* functor MTPRecursion *)
