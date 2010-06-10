functor Elab (structure Print : PRINT) : ELAB = struct
  structure I = IntSyn
  structure M = ModSyn
  
  (* the following methods are all that the module system needs about the semantics of the non-modular syntax *)
  
  (*
     N: Normalized: no Redex, no EVar (SOME _)
     A: Abstracted: no EVar, no FVar, implicit arguments Pi-bound
     E: Abbrevs expanded: no NSDef
  *)

  (* check whether n = U : V can be a strict definition
     (only needed as an optimization to return ConDefs if possible) *)
  fun checkStrict(U : I.Exp, V : I.Exp) : bool = (Strict.check((U,V), NONE); true) handle Strict.Error _ => false
  (* check whether U has type/kind V *)
  (* pre: NAE *)
  fun checkType(U : I.Exp, V : I.Exp) : bool = (TypeCheck.check(U,V); true) handle TypeCheck.Error _ => false
  (* check whether U has type/kind V *)
  (* pre: NAE *)  
  fun checkEqual(U : I.Exp, U' : I.Exp) : bool = Conv.conv((U, I.id), (U', I.id))
  (* normalizes an expression *)
  (* pre: true; post: NE *)
  fun normalize(U : I.Exp) : I.Exp = Whnf.normalize(U, I.id)
  (* abstracts away free variables left over after type reconstruction *)
  (* pre: true; post: NAE, #1 is number of implicit arguments *) 
  fun abstract(U : I.Exp) : I.Exp = #2 (Abstract.abstractDecImp U)
  
  fun printExp(U : I.Exp) : string = Print.expToString(I.Null, U)
  
  exception Error of string                       (* raised on type-checking errors *)
  exception MissingCase of IDs.mid * IDs.cid      (* raised if partially defined module cannot be applied *)
  exception UnimplementedCase                                 (* raised for unimplemented cases *)

  (* auxiliary function that raises exceptions *)
  fun typingError(U, V, msg) =
     let
        val pU = printExp U
        val pV = printExp V
     in
        raise Error(msg ^ "\nexpression: " ^ pU ^ "\nexpected type: " ^ pV)
     end

  (* auxiliary function that raises exceptions *)
   fun defInstClash(defDom, defCod, defDomTrans, msg) =
      let
         val pdefDom = printExp defDom
         val pdefCod = printExp defCod
         val pdefDomTrans = printExp defDomTrans
      in
         raise Error(msg ^ "definition: " ^ pdefDom ^ "\ntranslation of definition: " ^ pdefDomTrans ^
            "\ninstantiation: " ^ pdefCod)
      end

  (********************** type checking morphisms **********************)

  (* auxiliary methods to retrieve the list of morphisms included into a link *)
  (* more elegant: inclMorphs : Morph -> Morph listM then no case-split needed in restrictMorph *)
  fun inclMorphsView(m : IDs.mid) =
      List.mapPartial (fn M.ObjMor mor => SOME mor | _ => NONE) (M.modInclLookup m)
  fun inclMorphsStr(insts) =
      List.mapPartial (fn i => case i of M.InclInst(cid, _, mor) => SOME mor | _ => NONE) insts

  (* computes domain of a morphism without type-checking it *)
  fun domain(mor : M.Morph) : IDs.mid = case mor
    of M.MorView m => let val M.ViewDec(_, _, dom, _, _) = M.modLookup m in dom end
     | M.MorStr s => M.strDecDom (M.structLookup s)
     | M.MorComp(m,_) => domain m
     | M.MorId m => m
  
  (* computes codomain of a morphism without type-checking it *)
  fun codomain(mor : M.Morph) : IDs.mid = case mor
    of M.MorView m => let val M.ViewDec(_, _, _, cod, _) = M.modLookup m in cod end
     | M.MorStr s => IDs.midOf(s)
     | M.MorComp(_,m) => codomain m
     | M.MorId m => m
  
  (* reconstructs a morphism
     - computes domain and codomain of a morphism
     - adds omitted implicit morphism
     - composibility of morphisms is co-/contravariant with respect to inclusions
     - returns (dom, cod, reconmor); raises exception iff ill-formed *)
  fun reconMorph(M.MorComp(mor1,mor2)) =
        let
           val (d1,c1,m1) = reconMorph mor1
           val (d2,c2,m2) = reconMorph mor2
        in
           if M.sigIncluded(c1,d2)
           then (d1,c2, M.MorComp(m1,m2))
           else case M.implicitLookup(c1, d2)
              of SOME m => (d1, c2, M.MorComp(m1, M.MorComp(m, m2)))
               | NONE => raise Error("morphisms not composable")
        end
    | reconMorph(M.MorId m) = (m,m, M.MorId m)
    | reconMorph(M.MorStr s) = ((M.strDecDom (M.structLookup s), IDs.midOf(s), M.MorStr s)
                              handle M.UndefinedCid _ => raise Error("non-structure symbol reference in morphism"))
    | reconMorph(M.MorView m) =
        let
           val M.ViewDec(_, _, dom, cod, _) = M.modLookup m
                                        handle M.UndefinedMid _ => raise Error("non-view module reference in morphism")
        in
           (dom, cod, M.MorView m)
        end

  (* like reconmorph, but additionally checks against given domain/codomain
     returns the reconstructed morphism *)
  fun checkMorph(mor, dom, cod) =
     let
     	val (d,c, mor2) = reconMorph mor
     	val inclBefore = M.sigIncluded(dom,d)
        val implBefore = if inclBefore then NONE else M.implicitLookup(dom, d)
        val inclAfter  = M.sigIncluded(c,cod)
        val implAfter  = if inclAfter then NONE else M.implicitLookup(c, cod)
     in
     	case (inclBefore, implBefore, inclAfter, implAfter)
     	  of (true, _, true, _) => mor2
     	   | (true, _, false, SOME m) => M.MorComp(mor2, m)
     	   | (false, SOME m, true, _) => M.MorComp(m, mor2)
     	   | (false, SOME m, false, SOME n) => M.MorComp(m, M.MorComp(mor2, n))
           | _ => raise Error("morphism does not have expected type")
     end

  (* restricts a morphism to a domain, returns path in the signature graph, i.e., a list of links
     pre: mor is well-formed, newdom is included into domain(mor) (case 1,2,3a)
     post: restrictMorph(mor, newdom)
       is equal to mor and consists of only MorView _ or MorStr _ such that
       - definitions are expanded
       - the domain of the first link is newdom
       - the domain of each link is the codomain of the predecessor (i.e., includes are expanded)
       - in particular, result is nil if the restriction of mor is the identity 
   *)
  fun restrictMorph(M.MorComp(mor1,mor2), newdom) =
      let val rmor1 = restrictMorph(mor1, newdom)
          val cod = codomain rmor1
          val rmor2 = restrictMorph(mor2, cod)
      in
      	  M.MorComp(rmor1, rmor2)
      end
    | restrictMorph(M.MorId m, newdom) = M.MorId newdom
    | restrictMorph(M.MorStr c, newdom) = (
        case M.structLookup c
          of M.StrDef(_,_,_,mor,_) => restrictMorph (mor, newdom)
           | M.StrDec(_,_,dom, insts,_,_) =>
              if dom = newdom then M.MorStr c
              else restrictFirst(inclMorphsStr insts, newdom)
      )
    | restrictMorph(M.MorView m, newdom) =
       let val M.ViewDec(_, _, dom, _, _) = M.modLookup m
       in if dom = newdom
          then M.MorView m
          else restrictFirst(inclMorphsView m, newdom)
       end
  (* applies restrictMorph to the first restrictable morphism in a list of morphism *)
  and restrictFirst(mor :: tl, newdom) =
      if M.sigIncluded(newdom, domain(mor))
      then restrictMorph(mor, newdom)
      else restrictFirst(tl, newdom)
    | restrictFirst(nil, newdom) = M.MorId newdom
  
  (* auxiliary methods *)
  fun headToExp h = I.Root(h, I.Nil)
  fun cidToExp c = (case (M.sgnLookup c)
		      of (I.ConDec _) => headToExp(I.Const c)
		       | (I.ConDef _) => headToExp (I.Def c)
		       | (I.AbbrevDef _) => headToExp (I.NSDef c))
  fun BVar' i = headToExp (I.BVar i)

  (* morphism application
     pre: U is well-formed term over the domain of mor
     pre: mor is well-formed (all implicit morphisms filled in)
     post: U is well-formed term over the codomain of mor
   *)
  fun applyMorph(U, mor) =
     let
     	val (dom, cod, _) = reconMorph mor
     	fun A(I.Uni L) = I.Uni L
     	  | A(I.Pi((D, P), V)) = I.Pi((ADec D, P), A V)
     	  | A(I.Root(H, S)) = I.Redex(AHead H, ASpine S)  (* return Redex because AHead H need not be a Head again *)
     	  | A(I.Redex(U, S)) = I.Redex(A U, ASpine S)
     	  | A(I.Lam(D, U)) = I.Lam(ADec D, A U)
(*     	  | A(I.EVar(E, C, U, Constr)) = impossible by precondition *)
          | A(I.EClo(U,s)) = I.EClo(A U, ASub s)
(*          | A(I.AVar(I)) = impossible by precondition *)
          | A(I.FgnExp(cs, F)) = raise UnimplementedCase
          | A(I.NVar n) = I.NVar n
        and AHead(I.BVar k) = headToExp(I.BVar k)
          | AHead(I.Const c) = ACid c            (* apply morphism to constant *)
          | AHead(I.Proj(b,k)) = headToExp(I.Proj (ABlock b, k))
          | AHead(I.Skonst c) = ACid c           (* apply morphism to constant *)
          | AHead(I.Def d) = A (M.constDef d)
          | AHead(I.NSDef d) = A (M.constDef d)
          | AHead(I.FVar(x, U, s)) = headToExp(I.FVar(x, A U, ASub s))
          | AHead(I.FgnConst(cs, condec)) = raise UnimplementedCase
        and ASpine(I.Nil) = I.Nil
          | ASpine(I.App(U,S)) = I.App(A U, ASpine S)
          | ASpine(I.SClo(S,s)) = I.SClo(ASpine S, ASub s)
        and ASub(I.Shift n) = I.Shift n
          | ASub(I.Dot(Ft,s)) = I.Dot(AFront Ft, ASub s)
        and AFront(I.Idx k) = I.Idx k
          | AFront(I.Exp U) = I.Exp (A U)
          | AFront(I.Axp U) = I.Axp (A U)
          | AFront(I.Block b) = I.Block (ABlock b)
          | AFront(I.Undef) = I.Undef
        and ADec(I.Dec(x,V)) = I.Dec(x, A V)
(*          | ADec(I.BDec(v,(l,s))) = impossible by precondition *)
          | ADec(I.ADec(v,d)) = I.ADec(v,d)
          | ADec(I.NDec v) = I.NDec v
        and ABlock(I.Bidx i) = I.Bidx i
(*          | ABlock(I.LVar(b,s,(c,s'))) = impossible by precondition  *)
          | ABlock(I.Inst l) = I.Inst (List.map A l)
(*      and AConstr(_) = impossible by precondition  *)
        (* apply morphism to constant *)
        and ACid(c) =
           let val m = IDs.midOf c
           in
              case (mor, valOf (M.symVisible(c,dom))) (* if NONE, U would be ill-formed *)
                (* structure applied to local symbol: apply morphism by applying structMapLookup *)
                of (M.MorStr(s), M.Self) => cidToExp(valOf(M.structMapLookup (s,c)))    (* get the cid to which s maps c *)
                (* view applied to local symbol: apply morphism by looking up instantiation of view *)
                 | (M.MorView(v), M.Self) => (
                     let val M.SymConInst (M.ConInst(_, _, exp)) = M.symLookup(v, IDs.lidOf c)
                     in exp
                     end
                     handle Bind => raise MissingCase(v,c)
                   )
                 (* identity morphism *)
                 | (M.MorId _, _) => cidToExp c
                 (* composed morphism: apply components separately *)
                 | (M.MorComp(mor1, mor2), _) => applyMorph(applyMorph(cidToExp(c), mor1), mor2)
                 (* morphism applied to non-local symbol *)
                 | (_, M.Ancestor _) => cidToExp c (* symbol declared in ancestor: identity *)
                 | (_, M.AncIncluded) => cidToExp c (* symbol included into ancestor: identity *)
                 | (mor, M.Included _) => applyMorph(cidToExp c, restrictMorph(mor, m))
                     (* symbol declared in included signature: restrict morphism to obtain included morphism  *)
           end
     in
     	A U
     end

(****************************** Logical Relations *******************************************)

  (* computes domain of a relation without type-checking it *)
  fun domainRel(M.Rel m) = let val M.RelDec(_, _, dom, _, _) = M.modLookup m in dom end
    | domainRel(M.RelComp(mor,_)) = domain(mor)
  
  (* computes codomain of a relation without type-checking it *)
  fun codomainRel(M.Rel m) = let val M.RelDec(_, _, _, cod, _) = M.modLookup m in cod end
    | codomainRel(M.RelComp(_,rel)) = codomainRel(rel)

  (* reconstructs a logical relation
     returns (dom, cod, mors, reconrel); raises exception iff ill-formed *)
  fun reconRel(M.Rel m) =
        let
           val M.RelDec(_, _, dom, cod, mors) = M.modLookup m
                                        handle M.UndefinedMid _ => raise Error("bad identifier in logical relation")
        in
           (dom, cod, mors, M.Rel m)
        end
    | reconRel(M.RelComp(mor, rel)) =
       let
       	 val (mdom, mcod, mrec) = reconMorph mor
       	 val (rdom, rcod, rmors, rrec) = reconRel rel
       	 val precomp =
           if M.sigIncluded(mcod,rdom)
           then mrec
           else case M.implicitLookup(mcod, rdom)
             of SOME m => M.MorComp(mrec, m)
              | NONE => raise Error("morphism and logical relation not composable")
       in
       	  (mdom, rcod, List.map (fn x => M.MorComp(precomp, x)) rmors, M.RelComp(precomp, rrec))
       end
  
  (* checks a logical relation against domain, codomain, and a list of morphism *)
  fun checkRel(rel, dom, cod, mors) =
     let
     	 val (rdom, rcod, rmors, rrel) = reconRel rel
     	 val rmors' = List.map (fn x => checkMorph(x, dom, cod)) mors
     	 val _ = if rmors = rmors' (* @FR: too strict - definitions are not expanded *)
     	         then ()
     	         else raise Error("logical relation does not relate expected morphisms")
         val inclBefore = M.sigIncluded(dom,rdom)
         val implBefore = if inclBefore then NONE else M.implicitLookup(dom, rdom)
         val inclAfter  = M.sigIncluded(rcod,cod)
     in
     	case (inclBefore, implBefore, inclAfter)
     	  of (true, _, true) => rrel
     	   | (false, SOME m, true) => M.RelComp(m, rrel)
           | _ => raise Error("logical relation does not have expected type")
     end

  (* restricts a logical relation to a domain, returns path in the signature graph, i.e., a list of atomic relations
     pre: rel is well-formed, newdom is included into the domain of rel (case 1,2,3a)
     post: restrictRel(mor, newdom) of type M.Rel list
       is equal to rel and consists of only MorRel such that
       - the domain of the first atomic relation is newdom
       - in particular, result is nil if the restriction of rel is the identity 
   *)
  fun restrictRel(M.Rel m, newdom) =
       let val M.RelDec(_, _, dom, _, _) = M.modLookup m
       in if dom = newdom then M.Rel m
                          else restrictRelFirst(M.modInclLookup m, newdom)
       end
    | restrictRel(M.RelComp(mor,rel), newdom) =
      let val rmor = restrictMorph(mor, newdom)
          val cod = codomain rmor
          val rrel = restrictRel(rel, cod)
      in
      	  M.RelComp(rmor, rrel)
      end

  (* applies restrictRel to the first restrictable relation in a list of relations *)
  and restrictRelFirst(M.ObjRel rel :: tl, newdom) =
      if M.sigIncluded(newdom, domainRel(rel))
      then restrictRel(rel, newdom)
      else restrictRelFirst(tl, newdom)
    | restrictRelFirst(_ :: tl, newdom) = restrictRelFirst(tl, newdom) (* list of includes may contain signatures *)
    | restrictRelFirst(nil, newdom) = raise UnimplementedCase (* should be the identity relation but that cannot be expressed in LF type theory *)
  
  fun mormap u mors = List.map (fn m => applyMorph(u,m)) mors
  (* appy all morphisms to expression, return a spine *)
  fun morspine u mors : I.Spine = List.foldr I.App I.Nil (mormap u mors)
  
  (* logical relation application
     we write applyRel(U, SOME C, rel) as rel^C(U)
     pre: rel is a well-formed relation between a list of morphisms m_1, ..., m_n with domain dom and codomain cod
     pre: U is well-formed expression over dom in context G
     pre: if U is a kind, then tp is SOME C where C:U is the type family to which rel is applied
     post: if G |- U:K:kind over dom, then rel(G) |- rel(U):rel^C(K):kind over cod
     post: if G |- U:V:type over dom, then rel(G) |- rel(U):rel(V) m_1(V) ... m_n(V):type over cod
     contexts/spines over dom of length m go to contexts/spines of length m*(n+1)
        by applying the n morphism and the logical relation
   *)
  fun applyRel(U, COpt, rel) =
     let
     	val (dom, cod, mors, _) = reconRel rel
     	val n = List.length mors
        fun A u = A'(u,NONE)
        (* as morspine u mors but returns a context *)
        and MC u : I.Dec I.Ctx = List.foldl (fn (e,rest) => I.Decl(rest,I.Dec(I.NoVarInfo, e))) I.Null (mormap u mors)
     	and A'(I.Uni I.Kind, _) = I.Uni I.Kind
     	  | A'(I.Uni I.Type, SOME C) = I.PPi((MC C, I.No), I.Uni I.Type) (* rel^C(type) = m_1(C) -> ... -> m_n(C) -> type *)
     	  | A'(I.Pi((dec, dep), V), SOME C) = 
              (* rel^C(Pi dec. K) = Pi rel(dec).rel^{shift(C) 0}(K) *)
     	      let val newC = I.Redex(I.EClo(C, I.shift), I.App(BVar' 0, I.Nil))
     	      in I.PPi((ADec dec, I.Maybe), A'(V, SOME newC)) (* dep instead of I.Maybe? *)
     	      end
     	  | A'(P as I.Pi((dec, dep), V), _) =
     	      (* rel(Pi dec. V) = lam f_1:m_1(P). ... lam f_n:m_n(P). Pi rel(dec). (rel(V) (f_1 x_1) ... (f_n x_n)) *)
     	      let
     	      	 val nto1 = List.tabulate(n, fn x => n - x)                                  (* [n,...,1] *)
     	      	 val fx = List.map (fn i => I.Root(I.BVar(n+i), I.App(BVar' i, I.Nil))) nto1 (* [f_1 x_1, ..., f_n x_n] *)
     	      in I.LLam(MC P, I.PPi((ADec dec, I.Maybe), I.Redex(A V, List.foldr I.App I.Nil fx)))
     	      end
     	  | A'(I.Lam(dec, U), _) = I.LLam(ADec dec, A U)  (* both on type and on term level *)
     	  | A'(I.Redex(U, S), _) = I.Redex(A U, ASpine S)
     	  | A'(I.Root(H, S), _) = I.Redex(AHead H, ASpine S)
          | A'(I.EClo(U,s), _) = raise UnimplementedCase
          | A'(I.FgnExp(cs, F), _) = raise UnimplementedCase
          | A'(I.NVar n, _) = raise UnimplementedCase
(*        | A(I.AVar(I)) = impossible by precondition *)
(*     	  | A'(I.EVar(E, C, U, Constr)) = impossible by precondition *)
        and ADec(I.Dec(x,V)) : I.Dec I.Ctx = I.Decl(MC V, I.Dec(x,I.Redex(A V, morspine (BVar' 0) mors)))
            (* rel(x:A) =  x_1:m_1(A), ..., x_n:m_n(A), x:(rel(A) x_1 ... x_n) *)
(*        | ADec(I.BDec(v,(l,s))) = impossible by precondition *)
          | ADec(I.ADec(v,d)) = raise UnimplementedCase
          | ADec(I.NDec v) = raise UnimplementedCase
        and ASpine(I.Nil) = I.Nil
          | ASpine(I.App(U,S)) = List.foldr I.App (ASpine S) ((mormap U mors) @ [A U])
              (* rel(t_1 ... t_r) = m_1(t_1) ... m(t_1) rel(t_1)   ...   m_1(t_r) ... m(t_r) rel(t_r) *)
          | ASpine(I.SClo(S,s)) = raise UnimplementedCase
        and AHead(I.BVar k) = headToExp(I.BVar (k * (n+1)))
          | AHead(I.Const c) = ACid c
          | AHead(I.Skonst c) = ACid c
          | AHead(I.Def d) = A (M.constDef d)
          | AHead(I.NSDef d) = A (M.constDef d)
          | AHead(I.Proj(b,k)) = raise UnimplementedCase
          | AHead(I.FVar(x, U, s)) = raise UnimplementedCase
          | AHead(I.FgnConst(cs, condec)) = raise UnimplementedCase
(*      and ASub(I.Shift n) = I.Shift n
          | ASub(I.Dot(Ft,s)) = I.Dot(AFront Ft, ASub s)
        and AFront(I.Idx k) = I.Idx k
          | AFront(I.Exp U) = I.Exp (A U)
          | AFront(I.Axp U) = I.Axp (A U)
          | AFront(I.Block b) = I.Block (ABlock b)
          | AFront(I.Undef) = I.Undef
        and ABlock(I.Bidx i) = I.Bidx i
          | ABlock(I.LVar(b,s,(c,s'))) = impossible by precondition
          | ABlock(I.Inst l) = I.Inst (List.map A l)
        and AConstr(_) = impossible by precondition
*)
        (* apply relation to constant *)
        and ACid(c) =
           let val m = IDs.midOf c
           in
              case (rel, valOf (M.symVisible(c,dom))) (* if NONE, U would be ill-formed *)
                (* relation applied to local symbol: apply relation by looking up case *)
                of (M.Rel(r), M.Self) => (
                     let val M.SymConCase (M.ConCase(_, _, exp)) = M.symLookup(r, IDs.lidOf c)
                     in exp
                     end
                     handle Bind => raise MissingCase(r,c)
                   )
                 | (M.RelComp(mor, r), M.Self) => applyRel(applyMorph(cidToExp c, mor), NONE, r)
                 (* relation applied to non-local symbol *)
                 | (_, M.Ancestor _) => raise UnimplementedCase  (* identity relation cannot be expressed in LF type theory *) 
                 | (_, M.AncIncluded) => raise UnimplementedCase (* identity relation cannot be expressed in LF type theory *)
                 | (rel, M.Included _) => applyRel(cidToExp c, NONE, restrictRel(rel, m))
                     (* symbol declared in included signature: restrict relation to obtain included relation *)
           end
     in
        A'(U, COpt)
     end

  (* computes the expected type of rel(U) for U:V *)
  fun expType(c, rel) = raise UnimplementedCase
   (* case val V = M.constType c
                        of => normalize (applyRel(V, SOME (cidToExp c), rel))
                         | => normalize (I.Redex(applyRel(V, NONE, rel), morspine (cidToExp c) mors)) *)

  (********************** checking module level declarations **********************)
  
  (* checks an instantiation in a link, returns reconstructed instantiation *)
  fun checkSymInst(ci as M.ConInst(con, _, term)) =
      let
     	val v = M.currentMod()
     	val typ = M.constType con
     	val expTyp = applyMorph(typ, M.MorView v)
     in
     	if checkType(term, expTyp)
     	then ci
        else raise Error("type mismatch")
     end
    | checkSymInst(M.StrInst(str, org, mor)) =
     let
     	val expDom = M.strDecDom (M.structLookup str)
     	val newmor = checkMorph(mor, expDom, M.currentTargetSig())
     	(* equality constraints checked during flattening *)
     in
     	M.StrInst(str, org, newmor)
     end
    | checkSymInst(M.InclInst(cid, org, mor)) =
      let
      	 val M.SymIncl(M.SigIncl(expDom,_)) = M.symLookup cid
         val newmor = checkMorph(mor, expDom, M.currentTargetSig())
      in
         M.InclInst(cid, org, newmor)
      end

  fun checkSymCase(cc as M.ConCase(con, _, term)) =
      let
     	 val r = M.currentMod()
     	 val expTyp = expType(con, M.Rel r)
      in
         if checkType(term, expTyp)
         then cc
         else raise Error("type mismatch")
      end
    | checkSymCase(M.StrCase(str, org, rel)) =
      let
         val M.RelDec(_,_,dom, cod, mors) = M.modLookup (M.currentMod())
     	 val expDom = M.strDecDom (M.structLookup str)
     	 val newrel = checkRel(rel, expDom, cod, List.map (fn m => M.MorComp(M.MorStr str, m)) mors)
      in
         M.StrCase(str, org, newrel)
      end
    | checkSymCase(M.InclCase(cid, org, rel)) =
      let
         val M.RelDec(_,_,dom, cod, mors) = M.modLookup (M.currentMod())
      	 val M.SymIncl(M.SigIncl(expDom,_)) = M.symLookup cid
     	 val newrel = checkRel(rel, expDom, cod, List.map (fn m => M.MorComp(M.MorStr cid, m)) mors)
      in
         M.InclCase(cid, org, newrel)
      end

  (* auxiliary function of findClash
     if s is in forbiddenPrefixes, instantiations of s.c are forbidden
     if c is in forbiddenCids, instantiations of c are forbidden
  *)
  fun findClash'(nil, _, _) = NONE
    | findClash'(inst :: insts, forbiddenPrefixes, forbiddenCids) =
        let
           val c = M.symInstCid inst (* @FR: this is the only essential use of symInstCid; if abolished, InclInst would not need a cid thus making reconstruction a lot simpler *)
        in
           (* check whether c is in the list of cids of forbidden cids *)
           if List.exists (fn x => x = c) forbiddenCids
           then SOME(c)
           else
              let
              	 (* get the list of proper prefixes of c *)
                 val prefixes = List.map #1 (M.symQid c)
              in
                 (* check whether a prefix of c is in the list of forbidden prefixes *)
                 if List.exists (fn p => List.exists (fn x => x = p) forbiddenPrefixes) prefixes
            	 then SOME(c)
            	 (* forbid futher instantiations of
            	    - anything that has c as a prefix
            	    - c and any prefix of c *)
                 else findClash'(insts, c :: forbiddenPrefixes, c :: prefixes @ forbiddenCids)
              end
        end
  (* checks whether two instantiations in insts clash
     - return NONE if no clash
     - returns SOME c if an instantation for c is the first one leading to a clash
     a clash arises if there are instantiations for both
     - c and c, or
     - s and s.c
  *)
  fun findClash(insts) = findClash'(insts, nil, nil)

  (* checks whether the ancestors of the domain of a link are covered by the link
     This applies to inclusions, structures, and views.
     Any link dom -> cod must translate all symbols declared in ancestors of dom.
       By definition, morphism application is the identity for all symbols declared in ancestors of dom.
     Therefore, all ancestors of dom must also be ancestor_or_selfs of cod,
     Equivalently, we can say that dom must be visible/accessible for cod.
     Note that ancestors are pairs of an mid and the smallest invisible lid.
       Thus sister signatures with intermediate declarations do not have the same ancestors.
   *)
  fun checkAncestors(dom, cod) =
    let
       val domCid = M.midToCid dom
       val domPar = IDs.midOf domCid
       val codAncs = List.mapPartial
                     (fn M.ObjSig(a, M.Ancestor p) => SOME (a, M.midToCid p) | _ => NONE)
                     (M.modInclLookup cod)
       (* this is called with l < l' iff the morphism is a view whose domain is declared after the codomain
        in that case there may only be module declarations between domain and codomain *)
       fun onlyModsBetween(m, l, l') =
          if l >= l' then true
          else (case M.symLookup (IDs.newcid(m,l))
                  of M.SymMod _ => true
                   | _ => false
                ) andalso onlyModsBetween(m, l + 1, l')
       val _ = if domPar = cod orelse
                  List.exists (fn (a,c) => domPar = a andalso onlyModsBetween(a, IDs.lidOf c, IDs.lidOf domCid)) codAncs
               then ()
               else raise Error("the parent of the domain of a morphism must be ancestors of the codomain")
    in
       ()
    end

  (* checks whether the signatures included into the domain of a link are covered by the link
     Since include is transitive, this only applies to structures and views.
     A structure or view dom -> cod must include a morphism m_i : d_i -> com
       for every signature d_i directly included into dom.
       If m_i is not given, the identity is assumed, in which case d_i must also be included into cod.
     If there is a diamond situation with d included into d_1 and d_2, the morphisms m_1 and m_2 must agree on d. *)
  fun checkIncludes(dom : IDs.mid, cod : IDs.mid, mors : M.Morph list) =
    let
    	val domIncls = M.modInclLookup dom
    	val domAncIncls = List.mapPartial (fn M.ObjSig(d, M.AncIncluded) => SOME d | _ => NONE) domIncls
    	val domStrictIncls = List.mapPartial (fn M.ObjSig(d, M.Included _)  => SOME d | _ => NONE) domIncls
        fun checkSig(from) =
           let  (* paths among mors that are applicable to from *)
           	val applMorphs = List.mapPartial
                                (fn m => if M.sigIncluded(from, domain m)
                                         then SOME(restrictMorph(m, from))
                                         else NONE)
                                mors
                (* add the identity if from is also included via an ancestor *)
                val applMorphs' = if List.exists (fn x => x = from) domAncIncls
                                  then (M.MorId from) :: applMorphs
                                  else applMorphs
           in case applMorphs'
      	      of nil => (* check if identity path can be assumed, i.e., from included into cod *)
      	           if M.sigIncluded(from, cod)
      	           then ()
      	           else raise Error("signature " ^ M.modFoldName from ^ " included into " ^ M.modFoldName dom ^
                                          " but not into " ^ M.modFoldName cod)
               | hd :: tl => (* check equality of all paths (only path equality checked) *)
                   case List.find (fn x => not(x = hd)) tl
               	    of NONE => ()
                     | SOME _ => raise Error("conflicting translations for included signature " ^
                                  M.modFoldName from ^ " (implementation restriction: equality of morphisms only checked up to associativity and definition expansion)")
            end
    in
    	 (* check all strictly included signatures for applicable morphisms *)
         List.map checkSig domStrictIncls
    end

  (* checks structure declarations
     does not check:
     - all instantiations instantiate domain symbols with codomain expressions
       already checked during parsing/reconstruction
     - all instantiations are well-typed and preserve equalities
       will be checked during flattening
     postcondition: getInst yields all information that is needed to check the latter during flattening
  *)
  fun checkStrDec(M.StrDec(n, q, dom, insts, opens, impl)) =
       let
       	  val cod = M.currentMod()
          val newinsts = List.map (fn ci as M.ConInst _ => ci | i => checkSymInst i) insts;
          val _ = checkAncestors(dom, cod)
          val _ = case findClash newinsts
            of SOME c => raise Error("multiple (possibly induced) instantiations for " ^
                                      M.symFoldName c ^ " in structure declaration")
             | NONE => ();
          val _ = checkIncludes(dom, cod, inclMorphsStr insts)
       in
          M.StrDec(n, q, dom, newinsts, opens, impl)
       end
    | checkStrDec(M.StrDef(n, q, dom, mor, i)) =
        let val cod = M.currentMod()
            val _ = checkAncestors(dom, cod)
            val newmor = checkMorph(mor, dom, cod)
        in 
           M.StrDef(n, q, dom, newmor, i)
        end

  (* checks well-typedness condition for signature includes *)
  fun checkSigIncl(si as M.SigIncl (m,_)) =
       if M.inSignature()
       then checkAncestors(m, M.currentMod())
       else raise Error("including signatures only allowed in signatures")

  (* checks well-typedness conditions for modules (called at the end of the module *)
  fun checkModEnd(m) = case M.modLookup m
     of M.SigDec _ => ()
      | M.ViewDec(_, _, dom, cod, _) =>
        let
          val _ = checkAncestors(dom, cod)
          val _ = checkIncludes(dom, cod, inclMorphsView m)
          (* check totality of view: every undefined constant id of dom must have an instantiation in m *)
          (* what about block and skodec? *)
          fun checkDefined(c' : IDs.cid) = case M.symLookup c'
              of M.SymCon (I.ConDec _) => ((M.symLookup(m, IDs.lidOf c') ; ())
                 handle M.UndefinedCid _ => raise Error("view not total: missing instatiation for " ^ M.symFoldName c'))
               | _ => ()
        in
          M.sgnApp(dom, checkDefined)
        end
      | M.RelDec(_,_,dom,_,_) =>
        let
          (* check totality of relation: every undefined constant id of dom must have an instantiation in m *)
          fun checkDefined(c' : IDs.cid) = case M.symLookup c'
              of M.SymCon (I.ConDec _) => ((M.symLookup(m, IDs.lidOf c') ; ())
                 handle M.UndefinedCid _ => raise Error("logical relation not total: missing case for " ^ M.symFoldName c'))
               | _ => ()
        in
          M.sgnApp(dom, checkDefined)
        end
         
  (* checks well-typedness conditions for modules (called at the beginning of the module *)
  fun checkModBegin(_) = ()


 (********************** Flattening/elaboration **********************)

  (* auxiliary function of getInst, its first argument is a list of instantiations *)
  fun getInst'(nil, c, q) = NONE
    | getInst'(inst :: insts, c, q) = (
        case inst
           (* if c is instantiated directly, return its instantiation *)
           of M.ConInst(c', _, e) =>
              if c' = c
              then SOME e
              else getInst'(insts, c, q)
           (* if c can be addressed as c' imported via s, and if s is instantiated with mor,
              return the application of mor to c' *)
            | M.StrInst(s, _, mor) => (
                case IDs.preimageFromQid(s, q)
                  of SOME c' => SOME (applyMorph(cidToExp c', mor))
                   (* otherwise, try next instantiation *)
                   | NONE => getInst'(insts, c, q)
                )
            | M.InclInst _ => getInst'(insts, c, q)
      )
  (* finds an instantiation for cid c having qids q in a structure declaration
     this finds both explicit instantiations (c := e) and induced instantiations (s := mor in case c = s.c')
     in StrDefs, the instantiation is obtained by applying the definition of the structure to c
  *)
  fun getInst(M.StrDec(_,_,_, insts, _, _), c, q) = getInst'(insts, c, q)
    | getInst(M.StrDef(_,_,_,mor,_), c, _) = SOME (applyMorph(cidToExp c, mor))
  
  (* flattens a structure by computing all generated declarations (the order is depth first declaration order)
     - S: cid of the structure to be flattened
     - installConDec(c', condec): called for every generated constant declaration
       - c': the cid of the declaration in the domain
       - condec the generated declaration in the codomain
       - returns: the cid of the generated declaration
     - installStrDec: as installConDec, but for generated structure declarations
  *)
  (* variable naming convention:
     - flattened structure: upper case
     - declaration in domain: primed lower case
     - induced declaration in codomain: unprimed lower case
  *)
  fun flattenDec(S : IDs.cid, installConDec : IDs.cid * I.ConDec -> IDs.cid, installStrDec : IDs.cid * M.StrDec -> IDs.cid) =
     let
     	val Str = M.structLookup S
     	val Name = M.strDecName Str
     	val Q = M.strDecQid Str
     	val Dom = M.strDecDom Str
     	(* holds the list of pairs (s',s) of original and induced structure ids *)
     	val structMap : (IDs.cid * IDs.cid) list ref = ref nil
     	(* applies structMap to the first components of the pairs in q *)
     	fun applyStructMap(q: IDs.qid) = List.map (fn (x,y) => (#2 (valOf (List.find (fn z => #1 z = x) (!structMap))), 
     	                                                y)
     	                                          ) q
     	(* auxiliary function used in translated ConDec to unify the cases of ConDef and AbbrevDef *)
     	fun translateDefOrAbbrev(c', name', q', imp', def', typ', uni', anc'Opt) =
              let
                 val typ = normalize (applyMorph(typ', M.MorStr(S)))
                 val defold = applyMorph(def', M.MorStr(S))
                 val defnew = case getInst(Str, c', q')  
                    of SOME def =>  
                       (* if existing definitions are overridden, equality must be checked *)
                       if checkEqual(defold, def)
                       then normalize def
                       else defInstClash(def', def, defold, "definition/instantiation clash for " ^ M.symFoldName c')
                    | NONE => normalize defold
                 val _ = if checkType(defnew, typ)
                         then ()
                         else typingError(defnew, typ, "instantiation of " ^ M.symFoldName c' ^ " ill-typed\n")
                 val q = (S, c') :: (applyStructMap q')
              in 
                 if false (* not (anc'Opt = NONE) andalso uni' = I.Type andalso checkStrict(defnew, typ) *)
                 (* return a ConDef if the input was a term-level ConDef and strictness is preserved *)
                 then I.ConDef(Name @ name', q, imp', defnew, typ, uni', valOf anc'Opt) (* @CS: ancestor wrong *)
                 (* otherwise return AbbrevDef *)
                 else I.AbbrevDef(Name @ name', q, imp', defnew, typ, uni')
              end
     	   
     	(* translates a constant declaration (with id c') along S *)
        (* This function must be changed if this code is reused for a different internal syntax.
           It would be nicer to put it on toplevel, but that would be less efficient. *)
        fun translateConDec(c', I.ConDec(name', q', imp', stat', typ', uni')) =
              let
                 val typ = normalize (applyMorph(typ', M.MorStr(S)))
                 val q = (S, c') :: (applyStructMap q')
              in
                 case getInst(Str, c', q')
                   of SOME def =>
                       let val defn = normalize def
                       in if checkType(defn, typ)
                          then SOME(I.AbbrevDef(Name @ name', q, imp', defn, typ, uni')) (* @FR: can this be a ConDef? *)
                          else typingError(defn, typ, "instantiation of " ^ M.symFoldName c' ^ " ill-typed\n")
                       end
                    | NONE =>
                      SOME(I.ConDec(Name @ name', q, imp', stat', typ, uni'))
              end
           | translateConDec(c', I.ConDef(name', q', imp', def', typ', uni', anc')) =
               SOME(translateDefOrAbbrev(c', name', q', imp', def', typ', uni', SOME anc'))
           | translateConDec(c', I.AbbrevDef(name', q', imp', def', typ', uni')) =
               SOME(translateDefOrAbbrev(c', name', q', imp', def', typ', uni', NONE))
           | translateConDec(_, I.BlockDec(_, _, _, _)) = NONE
           | translateConDec(_, I.SkoDec(_, _, _, _, _)) = raise UnimplementedCase
        (* takes the declaration c' from the instantiated signature and computes and installs the translated declaration *)
     	fun flatten1(c' : IDs.cid) =
     	   case M.symLookup c'
              of M.SymCon(con') => (
                 case translateConDec(c', con')
                   of NONE => ()
                    | SOME con => (installConDec (c', con); ())
                 )
               | M.SymStr(str') =>
                (* translates a structure declaration (with id s') along S and adds an entry to structMap *)
                let
                   val s' = c'
                   val name' = M.strDecName str'
                   val q' = M.strDecQid str'
                   val dom' = M.strDecDom str'
                   val q = (S, s') :: (applyStructMap q')
                   val s = installStrDec (s', M.StrDef(Name @ name', q, dom', M.MorComp(M.MorStr(s'), M.MorStr(S)), false))
                   val _ = structMap := (s',s) :: (! structMap)
                in
                   ()
                end
               | M.SymIncl _ => ()
     in
     	(* calls flatten1 on all declarations of the instantiated signature (including generated ones) *)
     	M.sgnApp(Dom, flatten1)
     end

  fun flattenInst(instID : IDs.cid, installInst : M.SymInst -> IDs.cid) =
     let
        val viewID = IDs.midOf instID
        val M.SymStrInst(M.StrInst(s, _, mor)) = M.symLookup instID
        val (dom, _, _) = reconMorph mor
        fun flatten1(c' : IDs.cid) = 
            case M.symLookup c'
                 of M.SymCon _ =>
                   let
                      val c = valOf (M.structMapLookup(s,c'))
                      val defCod = normalize (applyMorph(cidToExp c', mor))
                      val typDomTrans = normalize(applyMorph(M.constType c, M.MorView viewID))
                      val _ = if checkType(defCod, typDomTrans) (* @FR: can this be skipped? *)
                              then ()
                              else raise Error("type mismatch in induced instantiation of " ^ M.symFoldName c)
                      val _ = case M.constDefOpt c
                                of NONE => ()
                                 | SOME defDom =>
                                   if checkEqual(applyMorph(defDom, M.MorView viewID), defCod)
                                   then ()
                                   else defInstClash(defDom, defCod, applyMorph(defDom, M.MorView viewID),
                                                     "definition/instantiation clash for " ^ M.symFoldName c)
                      val _ = installInst(M.ConInst(c, SOME instID, defCod))
                   in
                      ()
                   end
                  | M.SymStr _ =>
                     let
                     	val c = valOf (M.structMapLookup(s,c'))
                     	val _ = installInst(M.StrInst(c, SOME instID, M.MorComp(M.MorStr c', mor)))
                     in
                     	()
                     end
                  | M.SymIncl _ => ()
     in
        M.sgnApp(dom, flatten1)
     end

  fun flattenCase(caseid : IDs.cid, installCase : M.SymCase -> IDs.cid) =
     let
        val relid = IDs.midOf caseid
        val M.SymStrCase(M.StrCase(s, _, rel)) = M.symLookup caseid
        val (dom, _, mors, _) = reconRel rel
        fun flatten1(c' : IDs.cid) = 
            case M.symLookup c'
                 of M.SymCon condec =>
                   let
                      val c = valOf (M.structMapLookup(s,c'))
                      val inducedCase = normalize (applyRel(cidToExp c', NONE, rel))
                      val expectedType = expType(c, M.Rel relid)
                      val _ = if checkType(inducedCase, expectedType) (* @FR: can this be skipped? *)
                              then ()
                              else raise Error("type mismatch in induced case of " ^ M.symFoldName c)
                      val _ = case M.constDefOpt c
                                of NONE => ()
                                 | SOME defDom =>
                                   if checkEqual(applyRel(defDom, NONE, M.Rel relid), inducedCase)
                                   then ()
                                   else defInstClash(defDom, inducedCase, applyRel(defDom, NONE, M.Rel relid),
                                                     "definition/case clash for " ^ M.symFoldName c)
                      val _ = installCase(M.ConCase(c, SOME caseid, inducedCase))
                   in
                      ()
                   end
                  | M.SymStr _ =>
                     let
                     	val c = valOf (M.structMapLookup(s,c'))
                     	val _ = installCase(M.StrCase(c, SOME caseid, M.RelComp(M.MorStr c', rel)))
                     in
                     	()
                     end
                  | M.SymIncl _ => ()
                  | M.SymMod _ => ()
     in
        M.sgnApp(dom, flatten1)
     end
end