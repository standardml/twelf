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
		      structure MTPAbstract : MTPABSTRACT
			sharing MTPAbstract.IntSyn = IntSyn
			sharing MTPAbstract.StateSyn = StateSyn'
		      structure FunTypeCheck : FUNTYPECHECK
			sharing FunTypeCheck.FunSyn = FunSyn
		      structure MTPrint : MTPRINT
			sharing MTPrint.StateSyn = StateSyn'
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
      Lemma of int * F.For		(* Residual Lemma *)





	  fun paramPi ((nil, s), V) = V
	    | paramPi ((D :: G, s), V) = 
	        I.Pi ((I.decSub (D, s), I.Maybe), paramPi ((G, I.dot1 s),V)) 


	  fun ctxSub (nil, s) = nil
	    | ctxSub (D :: G, s) = I.decSub (D, s) :: ctxSub (G, I.dot1 s)


(*
	  fun paramPi ((G, s), V) =
	    let 
	      val G1 = F.listToCtx (ctxSub (G, s))
	      val w = MTPAbstract.weaken (G1, I.targetFam V)
	      val iw = Whnf.invert w
	      val G2 = Whnf.strengthen (iw, G1)
	      val V' = MTPAbstract.raiseType (G2, I.EClo (V, iw))
	    in
	      V'
	    end
*)
	
	  fun paramBlock (nil, s) = nil
	    | paramBlock (D :: G, s) = 
	        I.decSub (D, s) :: paramBlock (G, I.dot1 s)


(* Notes: restriction!!!! only in the case that function and type are living on the
   same level parameter cases are being generated.
   Other case soon to follow -cs *)

fun calc (n', (G0, F', O'), S as S.State (n, (G, B), (IH, OH), d, O, H, F)) =

let
    (* set_parameter (GB, X, k, sc, S) = S'

       Invariant:
       appends a list of recursion operators to S after
       instantiating X with all possible local parameters (between 1 and k)
    *)
    fun set_parameter (GB as (G1, B1), X as I.EVar (r, _, V, _), k, sc, Ds) =
	let 
	  (* set_parameter' ((G, B), k, Ds) = Ds'
	   
	     Invariant:
	     If    G1, D < G
	     and   
	  *)
	  fun set_parameter' ((I.Null, I.Null), _, Ds) =  Ds
	    | set_parameter' ((I.Decl (G, D), I.Decl (B, S.Parameter _)), k, Ds) = 
		let 
		  val D' as I.Dec (_, V') = I.decSub (D, I.Shift (k))
		  val Ds' = 
		    Trail.trail (fn () => 
				 if Unify.unifiable (G1, (V, I.id), (V', I.id))
				   andalso Unify.unifiable (G1, (X, I.id), (I.Root (I.BVar k, I.Nil), I.id))
				   then sc Ds
				 else Ds)
		in 
		  set_parameter' ((G, B), k+1, Ds')
		end
	    | set_parameter' ((I.Decl (G, D), I.Decl (B, _)), k, Ds) =
		set_parameter' ((G, B), k+1, Ds)

(* new *)
	  (* checkCtx (G2, (V, s)) = B'
	   
             Invariant:
	     if   G, G1 |- G2 ctx
             and  G, G1 |- s : G3  G3 |- V : L
             then B holds iff 
	     G1 = V1 .. Vn and G, G1, V1 .. Vi-1 |- Vi unifies with V [s o ^i] : L
	  *)
	  fun checkCtx (nil, (V2, s)) = false
	    | checkCtx (I.Dec (_, V1) :: G2, (V2, s)) = 
	      let 
		val B' = Trail.trail (fn () => Unify.unifiable (G, (V1, I.id), (V2, s)))
	      in
		B' orelse checkCtx (G2, (V2, I.comp (s, I.shift)))
	      end

	  fun alreadyIntroduced (I.Null, l) = false
	    | alreadyIntroduced (I.Decl (B, S.Parameter (SOME l')), l) = 
	      if l' = l then true else alreadyIntroduced (B, l)
	    | alreadyIntroduced (I.Decl (B, S.Parameter NONE), l) = 
		alreadyIntroduced (B, l)
	    | alreadyIntroduced (I.Decl (B, S.Assumption _), l) = 
		alreadyIntroduced (B, l)
	    | alreadyIntroduced (I.Decl (B, S.Lemma _), l) = 
		alreadyIntroduced (B, l)




	  fun abstract (_, nil) = nil
	    | abstract (G, Lemma (n, F) :: Ls) =
	       Lemma (n, F.All (F.Block (F.CtxBlock (NONE, G)), F)) :: abstract (G, Ls)

	  fun kont (GB3, s3) = 
	    let 
	      val S3 = S.State (n, GB3, (IH, OH), d, 
				  S.orderSub (O, s3),
				  map (fn (n', F') => (n', F.forSub (F', s3))) H,
				  F.forSub (F, s3))
	      val Ds' =  calc (n', (G0, F', O'), S3)
	    in 
	      Ds'
	    end


          (* introduceParameters (l, (G1, B1), G2, s, sc) = Ds'
       
             Invariant :
             If   |- G1 = G0, G0' ctx
	     and  |- B1 : G1 tags
	     and  l is a label
             and  G1 |- G2 ctx
	     and  G1 |- s : G0
             then G1 |- Ds' is a list of lemma decalartions
          *) 
	  fun introduceParameters (l, (G, B), D :: G2, s, sc) = 
	      let 
		val Ds' = introduceParameters (l, (I.Decl (G, D), I.Decl (B, S.Parameter (SOME l))), 
					       G2, I.comp (s, I.shift), sc)
	      in
	        Ds'
	      end
	    | introduceParameters (l, GB, nil, s, sc) = sc (GB, s)

          (* checkLabels (n, ops) = ops'
     
             Invariant:
             WORKS only for contexts with empty G1!!!
	     EACH parameter block can only used once.
	  *)
	  fun checkLabels (n, Ds) = 
	    if n < 0 then Ds
	    else
	      let 
		val F.LabelDec (name, nil, G2) = F.labelLookup n   
	(*	val Ds' = checkLabels (n-1, Ds)             (* not necessary!!! loop -cs *) *)
	      in
		if not (alreadyIntroduced (B, n)) andalso checkCtx (G2, (V, I.id)) then
		  Ds @ abstract (F.listToCtx (G2), introduceParameters (n, (G, B), G2, I.id, kont))
		else (* Ds' *) checkLabels (n-1, Ds) 
	      end
	    

(* newend *)


	in
	  checkLabels (F.labelSize ()-1, set_parameter' (GB, 1, Ds))
	end

    (* ltinit (GB, k, ((U1, s1), (V2, s2)), ((U3, s3), (V4, s4)), sc, Ds) = Ds'
     
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
    fun ltinit (GB, k, (Us, Vs), UsVs', sc, Ds) = 
          ltinitW (GB, k, Whnf.whnfEta (Us, Vs), UsVs', sc, Ds)
    and ltinitW (GB, k, (Us, Vs as (I.Root _, _)), UsVs', sc, Ds) =
          lt (GB, k, (Us, Vs), UsVs', sc, Ds)
      | ltinitW ((G, B), k, 
		 ((I.Lam (D1, U), s1), (I.Pi (D2, V), s2)), 
		 ((U', s1'), (V', s2')),
		 sc, Ds) =
          ltinit ((I.Decl (G, I.decSub (D1, s1) (* = I.decSub (D2, s2) *)),
		   I.Decl (B, S.Parameter NONE)), k+1, 
		  ((U, I.dot1 s1), (V, I.dot1 s2)), 
		  ((U', I.comp (s1', I.shift)), (V', I.comp (s2', I.shift))), 
		  sc, Ds)

    (* lt (GB, k, ((U, s1), (V, s2)), (U', s'), sc, Ds) = Ds'
     
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
    and lt (GB, k, (Us, Vs), (Us', Vs'), sc, Ds) = 
          ltW (GB, k, (Us, Vs), Whnf.whnfEta (Us', Vs'), sc, Ds)
    and ltW (GB, k, (Us, Vs), ((I.Root (I.Const c, S'), s'), Vs'), sc, Ds) = 
	  ltSpine (GB, k, (Us, Vs), ((S', s'), (I.constType c, I.id)), sc, Ds)
      | ltW (GB as (G, _), k, (Us, Vs), ((I.Root (I.BVar n, S'), s'), Vs'), sc, Ds) = 
	  if n <= k then  (* n must be a local variable *)
	    let 
	      val I.Dec (_, V') = I.ctxDec (G, n)
	    in
	      ltSpine (GB, k, (Us, Vs), ((S', s'), (V', I.id)), sc, Ds)
	    end
	  else Ds
      | ltW (GB, _, _, ((I.EVar _, _), _), _, Ds) = Ds
      | ltW (GB as (G, B), k, ((U, s1), (V, s2)), ((I.Lam (D as I.Dec (_, V1'), U'), s1'), 
					(I.Pi ((I.Dec (_, V2'), _), V'), s2')), sc, Ds) =
	if Subordinate.equiv (I.targetFam V, I.targetFam V1') (* == I.targetFam V2' *) then 
	  let  (* enforce that X gets only bound to parameters *) 
	    val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	    val sc' = fn Ds' => set_parameter (GB, X, k, sc, Ds')
	  in
	    lt (GB, k, ((U, s1), (V, s2)), 
		((U', I.Dot (I.Exp (X), s1')), 
		 (V', I.Dot (I.Exp (X), s2'))), sc', Ds)
	  end
	else
	  if Subordinate.below (I.targetFam V1', I.targetFam V) then
	    let 
	      val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	    in
	      lt (GB, k, ((U, s1), (V, s2)), 
		  ((U', I.Dot (I.Exp (X), s1')), 
		   (V', I.Dot (I.Exp (X), s2'))), sc, Ds)
	    end
	  else Ds

    and ltSpine (GB, k, (Us, Vs), (Ss', Vs'), sc, Ds) = 
          ltSpineW (GB, k, (Us, Vs), (Ss', Whnf.whnf Vs'), sc, Ds) 
    and ltSpineW (GB, k, (Us, Vs), ((I.Nil, _), _), _, Ds) = Ds
      | ltSpineW (GB, k, (Us, Vs), ((I.SClo (S, s'), s''), Vs'), sc, Ds) =
          ltSpineW (GB, k, (Us, Vs), ((S, I.comp (s', s'')), Vs'), sc, Ds)
      | ltSpineW (GB, k, (Us, Vs), ((I.App (U', S'), s1'), 
				   (I.Pi ((I.Dec (_, V1'), _), V2'), s2')), sc, Ds) = 
	let
	  val Ds' = le (GB, k, (Us, Vs), ((U', s1'), (V1', s2')), sc, Ds)
	in
	  ltSpine (GB, k, (Us, Vs), ((S', s1'), 
				 (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))), sc, Ds')
	end

    (* eq (GB, ((U, s1), (V, s2)), (U', s'), sc, Ds) = Ds'
     
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
    and eq ((G, B), (Us, Vs), (Us', Vs'), sc, Ds) = 
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

    and le (GB, k, (Us, Vs), (Us', Vs'), sc, Ds) = 
	let 
	  val Ds' = eq (GB, (Us, Vs), (Us', Vs'), sc, Ds)
	in
	  leW (GB, k, (Us, Vs), Whnf.whnfEta (Us', Vs'), sc, Ds')
	end

    and leW (GB as (G, B), k, ((U, s1), (V, s2)), ((I.Lam (D as I.Dec (_, V1'), U'), s1'), 
					(I.Pi ((I.Dec (_, V2'), _), V'), s2')), sc, Ds) =
	if Subordinate.equiv (I.targetFam V, I.targetFam V1') (* == I.targetFam V2' *) then 
	  let
	    val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	    val sc' = fn Ds' => set_parameter (GB, X, k, sc, Ds')
	  (* enforces that X can only bound to parameter *)
	  in                         
	    le (GB, k, ((U, s1), (V, s2)), 
		((U', I.Dot (I.Exp (X), s1')), 
		 (V', I.Dot (I.Exp (X), s2'))), sc', Ds)
	  end
	else
	  if Subordinate.below  (I.targetFam V1', I.targetFam V) then
	    let 
	      val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	    in
	      le (GB, k, ((U, s1), (V, s2)), 
		  ((U', I.Dot (I.Exp (X), s1')), 
		   (V', I.Dot (I.Exp (X), s2'))), sc, Ds)
	    end
	  else Ds
      | leW (GB, k, (Us, Vs), (Us', Vs'), sc, Ds) = lt (GB, k, (Us, Vs), (Us', Vs'), sc, Ds) 

	      
    (* ordlt (GB, O1, O2, sc, Ds) = Ds'
     
       Invariant:
       If   G |- O1 augmented subterms   
       and  G |- O2 augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all 
	    recursion operators of all instantiations of EVars s.t. O1 is
	    lexicographically smaller than O2
    *)
    fun ordlt (GB, S.Arg UsVs, S.Arg UsVs', sc, Ds) =  ltinit (GB, 0, UsVs, UsVs', sc, Ds)
      | ordlt (GB, S.Lex L, S.Lex L', sc, Ds) = ordltLex (GB, L, L', sc, Ds)
      | ordlt (GB, S.Simul L, S.Simul L', sc, Ds) = ordltSimul (GB, L, L', sc, Ds)


    (* ordltLex (GB, L1, L2, sc, Ds) = Ds'
     
       Invariant:
       If   G |- L1 list of augmented subterms   
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all 
	    recursion operators of all instantiations of EVars s.t. L1 is
	    lexicographically less then L2
    *)
    and ordltLex (GB, nil, nil, sc, Ds) = Ds
      | ordltLex (GB, O :: L, O' :: L', sc, Ds) =
        let 
	  val Ds' = Trail.trail (fn () => ordlt (GB, O, O', sc, Ds))
	in 
	  ordeq (GB, O, O', fn Ds'' =>  ordltLex (GB, L, L', sc, Ds''), Ds')
	end

    (* ordltSimul (GB, L1, L2, sc, Ds) = Ds'
     
       Invariant:
       If   G |- L1 list of augmented subterms   
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all 
	    recursion operators of all instantiations of EVars s.t. L1 is
	    simultaneously smaller than L2
    *)
    and ordltSimul (GB, nil, nil, sc, Ds) = Ds
      | ordltSimul (GB, O :: L, O' :: L', sc, Ds) = 
        let
	  val Ds'' = Trail.trail (fn () => ordlt (GB, O, O',
			fn Ds' => ordleSimul (GB, L, L', sc, Ds'), Ds))
	in 
	  ordeq (GB, O, O', fn Ds' => ordltSimul (GB, L, L', sc, Ds'), Ds'')
	end

    (* ordleSimul (GB, L1, L2, sc, Ds) = Ds'
     
       Invariant:
       If   G |- L1 list of augmented subterms   
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all 
	    recursion operators of all instantiations of EVars s.t. L1 is
	    simultaneously smaller than or equal to L2
    *)
    and ordleSimul (GB, nil, nil, sc, Ds) = sc Ds
      | ordleSimul (GB, O :: L, O' :: L', sc, Ds) =
          ordle (GB, O, O', fn Ds' => ordleSimul (GB, L, L', sc, Ds'), Ds)

	      
    (* ordeq (GB, O1, O2, sc, Ds) = Ds'
     
       Invariant:
       If   G |- O1 augmented subterms   
       and  G |- O2 augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all 
	    recursion operators of all instantiations of EVars s.t. O1 is
	    convertible to O2
    *)
    and ordeq ((G, B), S.Arg (Us, Vs), S.Arg (Us' ,Vs'), sc, Ds) =  
          if Unify.unifiable (G, Vs, Vs') andalso Unify.unifiable (G, Us, Us') then sc Ds else Ds
      | ordeq (GB, S.Lex L, S.Lex L', sc, Ds) = ordeqs (GB, L, L', sc, Ds)
      | ordeq (GB, S.Simul L, S.Simul L', sc, Ds) = ordeqs (GB, L, L', sc, Ds)
      
    (* ordlteqs (GB, L1, L2, sc, Ds) = Ds'
     
       Invariant:
       If   G |- L1 list of augmented subterms   
       and  G |- L2 list of augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all 
	    recursion operators of all instantiations of EVars s.t. L1 is
	    convertible to L2
    *)
    and ordeqs (GB, nil, nil, sc, Ds) = sc Ds
      | ordeqs (GB, O :: L, O' :: L', sc, Ds) = 
          ordeq (GB, O, O', fn Ds' => ordeqs (GB, L, L', sc, Ds'), Ds)

    (* ordeq (GB, O1, O2, sc, Ds) = Ds'
     
       Invariant:
       If   G |- O1 augmented subterms   
       and  G |- O2 augmented subterms
       and  Ds is a set of already calculuated possible states
       and  sc is success continuation
       then Ds' is an extension of Ds, containing all 
1	    recursion operators of all instantiations of EVars s.t. O1 is
	    convertible to O2 or smaller than O2
    *)
    and ordle (GB, O, O', sc, Ds) = 
	let 
	  val Ds' = Trail.trail (fn () => ordeq (GB, O, O', sc, Ds))
	in
	  ordlt (GB, O, O', sc, Ds')
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
      

    (*  createEVars' (G, G0) = s'
        
        Invariant : 
	If   |- G ctx
	and  |- G0 ctx
	then G |- s' : G0
	and  s' = X1 .. Xn where n = |G0|
    *)
    fun createEVars (G, I.Null) = I.Shift (I.ctxLength G)
      | createEVars (G, I.Decl (G0, I.Dec (_, V))) = 
          let 
	    val s = createEVars (G, G0)
	  in
	    I.Dot (I.Exp (I.newEVar (G, I.EClo (V, s))), s)
	  end



    val s' = createEVars (G, G0)
    val Os' = S.orderSub (O', s')
    val check' = check (G, n', s', G0, Os', IH, H, (F', s'))
    val Ds = if n < n' then ordle ((G, B), Os', O, check', nil)
	     else ordlt ((G, B), Os', O, check', nil)
in 
    Ds
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
(* ---------------- *)
      | skolem ((du, de), GB, w, F.All (F.Block (F.CtxBlock (name, G1)), F), sc) =
          skolem ((du+I.ctxLength G1, de), GB, w, F, 
		  fn (s, de') =>	
					(* s'  :  GB, Ds |- s : GB   *)
		     let 
		       val (s', V', F') = sc (s, de')                                         
					(* s'  : GB, Ds, G'[...] |- s' : GB, G *)
					(* V'  : maps (GB, Ds, G'[...] |- V type) to (GB, Ds |- {G'[...]} V type) *)
					(* F'  : maps (GB, Ds, G'[...] |- F for) to (GB, Ds |- {{G'[...]}} F for) *)
		       val s'' = F.dot1n (G1, s')
		     in
		       (s'', 
					(* _   : GB, Ds, G'[...], D[?] |- _ : GB, G, D *)
 			fn V => V' (paramPi ((F.ctxToList G1, s'), V)),  
					(* _   : maps (GB, Ds, G'[....], D[?] |- V : type) to  (GB, Ds, |- {G[....], D[?]} V : type) *)
			fn F => F' (F.All (F.Block (F.CtxBlock (name, F.listToCtx (paramBlock (F.ctxToList G1, s')))), F))
					(* _   : maps (GB, Ds, G'[....], D[?] |- F : for) to  (GB, Ds, |- {{G[....], D[?]}} F : for) *)
			)
		     end)	 
(* ----------------- *)
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


    (* selectFormula (n, G, (G0, F, O), S) = S'
      
       Invariant:
       If   G |- s : G0  and  G0 |- F formula and  G0 |- O order
       and  S is a state
       then S' is the state with 
       sc returns with all addition assumptions/residual lemmas for a certain
       branch of the theorem.
    *)
    fun selectFormula (n, (G0, F.All (F.Prim (D as I.Dec (_, V)), F), S.All (_, O)), S) =
 	  selectFormula (n, (I.Decl (G0, D), F, O), S)
      | selectFormula (n, (G0, F.And (F1, F2), S.And (O1, O2)), S) =
	let
	  val (n', S') = selectFormula (n, (G0, F1, O1), S)
	in
	  selectFormula (n, (G0, F2, O2), S')
	end
      | selectFormula (n, (G0, F, O), S) = 
	let
	  val Ds = calc (n, (G0, F, O), S)
	in
	  (n+1, updateState (S, (Ds, I.id)))
	end

    fun expand (S as S.State (n, (G, B), (IH, OH), d, O, H, F)) =
      let 
	val (_, S') = selectFormula (1, (I.Null, IH, OH), S)
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
