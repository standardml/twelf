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
  (* pre: U is NAE, U is strict definies of some constant
     post: result is ancestor info for ConDef *)
  fun ancestor(U: I.Exp) : I.Ancestor = M.ancestor(U)
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
  fun morTypingError(d,c,dom,cod, msg) =
        raise Error(msg ^ "\nmorphism: " ^ ModSyn.modFoldName d ^ " -> " ^ ModSyn.modFoldName c ^ 
                          "\nexpected type: " ^ ModSyn.modFoldName dom ^ " -> " ^ ModSyn.modFoldName cod)

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
  (* more elegant: inclMorphs : Morph -> Morph list then no case-split needed in restrictMorph *)
  fun inclMorphsView(m : IDs.mid) =
      List.mapPartial (fn M.ObjMor mor => SOME mor | _ => NONE) (M.modInclLookup m)
  fun inclMorphsStr(insts) =
      List.mapPartial (fn i => case i of M.InclInst(cid, _, _, mor) => SOME mor | _ => NONE) insts

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
               | NONE => raise Error("morphism with codomain " ^ M.modFoldName c1 ^
                                                   " and morphism with domain " ^ M.modFoldName d2 ^ " not composable")
        end
    | reconMorph(M.MorId m) = (m,m, M.MorId m)
    | reconMorph(M.MorStr s) = ((M.strDecDom (M.structLookup s), IDs.midOf(s), M.MorStr s)
                              handle M.UndefinedCid _ => raise Error("non-structure symbol reference in morphism "))
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
         | _ => morTypingError(d,c,dom,cod,"morphism does not have expected type")
     end

  (* restricts a morphism to a domain
     pre: mor is well-formed, newdom is included into domain(mor) (case 1,2,3a)
     post: restrictMorph(mor, newdom)
       is equal to mor and
       - definitions are expanded
       - the domain of the first link is newdom
       - the domain of each link is the codomain of the predecessor
       - in particular, result is MorId if the restriction of mor is the identity 
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
  
  (* filters a list of instantiations,
     pre: newdom is included into the domain of the structure with instantiations inst
     post: returns the instantiations of symbols that are visible to newdom *)
  fun restrictInsts(nil, newdom) = nil
    | restrictInsts(inst :: insts, newdom) =
      let val rest = restrictInsts(insts, newdom)
      in case inst
         of M.InclInst(i, _, from, mor) =>
            (* @FR: technically, we need to update the cid in the inst to c where M.Included c is the SigRelType of the inclusion
                    this is not done because we silently also permit M.Self *)
            if M.sigIncluded(from, newdom) then inst :: rest else rest
          | _ => if M.sigIncluded(IDs.midOf(M.symInstCid inst), newdom) then inst :: rest else rest
      end
    
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
(*        | A(I.AVar(I)) = impossible by precondition *)
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
                of
                 (* identity morphism *)
                 (M.MorId _, _) => cidToExp c
                 (* composed morphism: apply components separately *)
                 | (M.MorComp(mor1, mor2), _) => applyMorph(applyMorph(cidToExp(c), mor1), mor2)
                 (* symbol declared in ancestor: identity *)
                 | (_, M.Ancestor _) => cidToExp c
                 (* symbol included into ancestor: identity *)
                 | (_, M.AncIncluded) => cidToExp c
                 (* view applied to local symbol: apply morphism by looking up instantiation in view *)
                 | (M.MorView(v), M.Self) => (
                     let val M.SymConInst (M.ConInst(_, _, exp)) = M.symLookup(v, IDs.lidOf c)
                     in exp
                     end
                     handle Bind => raise MissingCase(v,c)
                          | M.UndefinedCid _ => raise MissingCase(v,c)
                   )
                 (* view applied to included symbol: apply restricted morphism *)
                 | (M.MorView v, M.Included _) => applyMorph(cidToExp c, restrictMorph(M.MorView v, m))
                 (* structure applied to local or included symbol: apply morphism by look up in M.structMap *)
                 | (M.MorStr(s), M.Self) => cidToExp(valOf(M.structMapLookup (s,c)))    (* get the cid to which s maps c *)
                 | (M.MorStr(s), M.Included i) =>
                    let val si = valOf(M.structMapLookup (s,i))    (* get the structure to which s maps the inclusion i *)
                    in cidToExp(valOf(M.structMapLookup (si,c)))    (* get the cid to which si maps c *)
                    end
           end
     in
     	A U
     end

(****************************** Logical Relations *******************************************)

   (* printing of expressions, for debugging
   fun printExp(I.Uni I.Kind) = "kind"
     | printExp(I.Uni I.Type) = "type"
     | printExp(I.Pi((dec, _), V)) = "({" ^ printDec dec ^ "} " ^ printExp V ^ ")"
     | printExp(I.Lam(dec, V)) = "([" ^ printDec dec ^ "] " ^ printExp V ^ ")"
     | printExp(I.Redex(U, S)) = (case S of I.Nil => printExp U | _ => "(" ^ printExp U ^ printSpine S ^ ")")
     | printExp(I.Root(H,S)) = (case S of I.Nil => printHead H | _ => "(" ^ printHead H ^ printSpine S ^ ")")
     | printExp(I.EClo(U,s)) = (case s of I.Shift 0 => printExp U | _ => "(" ^ printExp U ^ " @ " ^ printSub s ^ ")")
   and printDec(I.Dec(vi,V)) = let val name = case vi of I.VarInfo(SOME n, _, _, _) => n | _ => "_"
                                in name ^ ":" ^ printExp(V) end
   and printSpine(I.Nil) = ""
     | printSpine(I.App(U,S)) = " " ^ printExp U ^ printSpine S
   and printHead(I.BVar k) = Int.toString k
     | printHead(I.Const c) = M.symFoldName c
     | printHead(I.Def c) = M.symFoldName c
     | printHead(I.NSDef c) = M.symFoldName c
   and printSub(I.Shift 0) = ""
     | printSub(I.Shift k) = "^" ^ Int.toString k
     | printSub(I.Dot(Ft, s)) = printFront Ft ^ " " ^ printSub s
   and printFront(I.Idx k) = Int.toString k
     | printFront(I.Exp U) = printExp U
   *)
   
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
              | NONE => raise Error("morphism with codomain " ^ M.modFoldName mcod ^ 
                                    " and logical relation with domain " ^ M.modFoldName rdom ^ " not composable")
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
     	         else raise Error("bad morphisms in logical relation: " ^
     	           "expected " ^ IDs.mkString(List.map Print.morphToString rmors',"", " -> ","") ^
     	           "; found " ^ IDs.mkString(List.map Print.morphToString rmors,"", " -> ",""))
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
  
  (* logical relation application
     we write applyRel(U, SOME C, rel) as rel^C(U)
     pre: rel is a well-formed relation between a list of morphisms m_1, ..., m_n with domain dom and codomain cod
     pre: U is well-formed expression over dom in context G
     pre: if U is a kind, then COpt is SOME C where C:U is the type family to which rel is applied
     post: if G |- C:K:kind over dom, then rel(G) |- rel(C):rel^C(K):kind over cod
     post: if G |- U:V:type over dom, then rel(G) |- rel(U):rel(V) m_1(V) ... m_n(V):type over cod
     contexts/spines over dom of length m go to contexts/spines of length m*(n+1) over cod
        by applying the n morphisms and the logical relation
   *)

  (* The functions below take a parameter 'l: newvars list', which gives the shape of the context rel(G), lowest index first *)
  datatype newvars = DVar of int        (* DVar k   : k declarations induced by one G-declaration *)
                    | DOther of int      (* DOther k : k other declarations *)
  (* findVar(rel(G), i) returns the lowest index in the block induced by the G-declaration of i *)
  fun findVar(DVar(_) :: _, 1) = 1
    | findVar(DVar(k) :: tl, i) = findVar(tl, i-1) + k
    | findVar(DOther k :: tl, i) = findVar(tl, i) + k
  (* returns the number of blocks induced by G-declarations, i.e., the length of G *)
  fun nmbVars(DVar(_)::tl) = nmbVars(tl) + 1
    | nmbVars(DOther(_)::tl) = nmbVars(tl)
    | nmbVars(nil) = 0

  (* [(l_0,0), ..., (l_{n-1}, n-1)] *)
  fun zipWithIndex l = ListPair.zip(l, (List.tabulate(List.length l, fn x => x)))

  fun applyRel(U, COpt, rel) =
  let
     	val (dom, cod, mors, _) = reconRel rel
     	val n = List.length mors
     	val morsWithIndex = zipWithIndex mors
        (* morsub u = [m'_1(u), ..., m'_n(u)]
           m'_j(-) is application of m_j followed by the substitution subs_j : from m_j(G) to rel(G)
           which maps i to the corresponding variable in rel(G)
           if        G = x_r, ..., x_i, ..., x_1
           then rel(G) = ... x_i@m_n, ..., x_i@m_1, x_i@rel, ...   where x_i@rel has index p_i
                subs_j maps x_i to x_i@m_j
         *) 
      fun morsub u l =
          let
             val vars = List.tabulate(nmbVars l, fn i => findVar(l, i+1))  (* [p_1, ..., p_r] *)
             fun subs j = List.foldr (fn (i,rest) => I.Dot(I.Idx (i + n+1-j), rest)) I.id vars (* x_1@m_j Dot ... Dot x_r@m_j Dot id *)
          in List.map (fn (m,j) => I.EClo(applyMorph(u, m), subs (j+1))) morsWithIndex
          end
        (* similar to morsub u but returns the context m'_1(u), ..., m'_n(u) *)
      fun MC u l p: I.Dec I.Ctx =
           let
              fun varInfo i = case p of SOME pref => I.VarName(Int.toString i ^ "_" ^ pref) | NONE => I.NoVarInfo 
              (* each m'_i(u) must be shifted i-1 times *)
              val tps = List.map (fn (t,i) => (I.EClo(t, I.Shift i), i)) (zipWithIndex (morsub u l))
           in List.foldl (fn ((tp, i),rest) => I.Decl(rest,I.Dec(varInfo i, tp))) I.Null tps
           end
        (* applying to an expression *)
      fun A u l = A'(u,NONE, l)
      and A'(I.Uni I.Kind, _, _) = I.Uni I.Kind
     	  | A'(I.Uni I.Type, SOME C, l) = I.PPi((MC C l NONE, I.No), I.Uni I.Type)
     	       (* rel^C(type) = m_1(C) -> m_n(C) -> type *)
     	  | A'(I.Pi((dec, dep), V), SOME C, l) = 
              (* rel^C(Pi dec. K) = Pi rel(dec).rel^{shift(C) 1}(K) *)
     	      let val newC = I.Redex(I.EClo(C, I.shift), I.App(BVar' 1, I.Nil))
     	      in I.PPi((ADec dec l, I.Maybe), A'(V, SOME newC, DVar(n+1)::l)) (* dep instead of I.Maybe? *)
     	      end
     	  | A'(P as I.Pi((dec, dep), V), _, l) =
     	      (* rel(Pi dec. V) = lam f_1:m_1(P). ... lam f_n:m_n(P). Pi rel(dec). (rel(V) (f_1 x_1) ... (f_n x_n)) *)
     	      let
     	      	 val inds = List.tabulate(n, fn x => n+1 - x)                              (* [n+1,...,2] *)
     	      	 val fx = List.map (fn i => I.Root(I.BVar(n+i), I.App(BVar' i, I.Nil))) inds (* [f_1 x_1, ..., f_n x_n] *)
     	      in I.LLam(MC P l NONE, I.PPi((ADec dec (DOther(n)::l), I.Maybe), I.Redex(A V (DVar(n+1)::DOther(n)::l), List.foldr I.App I.Nil fx)))
     	      end
     	  | A'(I.Lam(dec, U), _, l) = I.LLam(ADec dec l, A U (DVar(n+1)::l))  (* both on type and on term level *)
     	  | A'(I.Redex(U, S), _, l) = I.Redex(A U l, ASpine S l)
     	  | A'(I.Root(H, S), _, l) = I.Redex(AHead H l, ASpine S l)
        | A'(I.EClo(U,s), _, _) = raise UnimplementedCase
        | A'(I.FgnExp(cs, F), _, _) = raise UnimplementedCase
        | A'(I.NVar n, _, _) = raise UnimplementedCase
(*      | A(I.AVar(I)) = impossible by precondition *)
(*      | A'(I.EVar(E, C, U, Constr)) = impossible by precondition *)
        (* applying to a declaration, returns context of length n+1 *)
        and ADec(I.Dec(vi,V)) l : I.Dec I.Ctx =
            let
               val I.VarInfo(name, _, _, _) = vi 
               val vars = List.tabulate(n, fn x => BVar' (n-x))  (* [n,...,1] *)
            in I.Decl(MC V l name, I.Dec(vi,I.Redex(A V (DOther(n)::l), List.foldr I.App I.Nil vars)))
            end
            (* rel(x:A) =  x_1:m_1(A), ..., x_n:m_n(A), x:(rel(A) x_1 ... x_n) *)
(*        | ADec(I.BDec(v,(l,s))) = impossible by precondition *)
          | ADec(I.ADec(v,d)) _ = raise UnimplementedCase
          | ADec(I.NDec v) _ = raise UnimplementedCase
        (* applying to a spine, returns spine of length m(n+1) *)
        and ASpine(I.Nil) _ = I.Nil
          | ASpine(I.App(U,S)) l = List.foldr I.App (ASpine S l) ((morsub U l) @ [A U l])
              (* rel(t_1 ... t_r) = m_1(t_1) ... m(t_1) rel(t_1)   ...   m_1(t_r) ... m(t_r) rel(t_r) *)
          | ASpine(I.SClo(S,s)) _ = raise UnimplementedCase
        and AHead(I.BVar k) l = BVar' (findVar(l, k))
          | AHead(I.Const c) _ = ACid c
          | AHead(I.Skonst c) _ = ACid c
          | AHead(I.Def d) l = A (M.constDef d) l
          | AHead(I.NSDef d) l = A (M.constDef d) l
          | AHead(I.Proj(b,k)) _ = raise UnimplementedCase
          | AHead(I.FVar(x, U, s)) _ = raise UnimplementedCase
          | AHead(I.FgnConst(cs, condec)) _ = raise UnimplementedCase
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
                of (M.Rel r, M.Self) => (
                     let val M.SymConCase (M.ConCase(_, _, exp)) = M.symLookup(r, IDs.lidOf c)
                     in exp
                     end
                     handle Bind => raise MissingCase(r,c) | UndefinedCid => raise MissingCase(r,c)
                   )
                 | (M.RelComp(mor, r), M.Self) => applyRel(applyMorph(cidToExp c, mor), NONE, r)
                 (* relation applied to non-local symbol *)
                 | (_, M.Ancestor _) => raise UnimplementedCase  (* identity relation cannot be expressed in LF type theory *) 
                 | (_, M.AncIncluded) => raise UnimplementedCase (* identity relation cannot be expressed in LF type theory *)
                 | (rel, M.Included _) => applyRel(cidToExp c, NONE, restrictRel(rel, m))
                     (* symbol declared in included signature: restrict relation to obtain included relation *)
           end
     in
        A'(U, COpt, nil)
     end

  (* computes the expected type of rel(U) for U:V *)
  fun expType(c, rel) =
     let val dec = M.sgnLookup c
         val V = I.conDecType dec
         val (_,_,mors,rel') = reconRel rel
     in case I.conDecUni dec
          of I.Kind => normalize (applyRel(V, SOME (cidToExp c), rel'))
           | I.Type =>
            let val sp = List.foldr I.App I.Nil (List.map (fn m => applyMorph(cidToExp c,m)) mors)
            in normalize (I.Redex(applyRel(V, NONE, rel), sp))
            end
     end

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
        else raise Error("type mismatch") (* this check is probably not necessary if called on reconstructed input *)
     end
    | checkSymInst(M.StrInst(str, org, mor)) =
     let
     	val expDom = M.strDecDom (M.structLookup str)
     	val newmor = checkMorph(mor, expDom, M.currentTargetSig())
     	(* equality constraints checked during flattening *)
     in
     	M.StrInst(str, org, newmor)
     end
    | checkSymInst(M.InclInst(cid, org, dom, mor)) =
      let
         val newmor = checkMorph(mor, dom, M.currentTargetSig())
      in
         M.InclInst(cid, org, dom, newmor)
      end

  fun checkSymCase(cc as M.ConCase(con, _, term)) =
      let
     	 val r = M.currentMod()
     	 val expTyp = expType(con, M.Rel r)
      in
         if checkType(term, expTyp)
         then cc
         else raise Error("type mismatch") (* this check is probably not necessary if called on reconstructed input *)
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
      	 val M.SymIncl(M.SigIncl(expDom,_,_)) = M.symLookup cid
      	 (* expDom ins included into dom for cases that have passed through reconstruction *)
     	 val newrel = checkRel(rel, expDom, cod, List.map(fn m => restrictMorph(m, expDom)) mors)
      in
         M.InclCase(cid, org, newrel)
      end

  (* auxiliary function of findClash
     if s is in forbiddenPrefixes, instantiations of s.c are forbidden
     if c is in forbiddenCids, instantiations of c are forbidden
     if d is in inclInstDoms, instantiations of symbols included into d are forbidden
     if d is in otherDoms, instantiations of a whole include from a signature that includes d are forbidden
  *)
  fun findClash'(nil, _, _,_,_) = NONE
    | findClash'(inst :: insts, forbiddenPrefixes, forbiddenCids, inclInstDoms, otherDoms) =
        let
           val c = M.symInstCid inst
         	 (* get the list of proper prefixes of c *)
           val prefixes = List.map #1 (M.symQid c)
           val m = IDs.midOf c
           val (inclInstDom, otherDom) = case inst
              of M.InclInst(i, _, dom, _) => ([dom], nil)
               | _ => (nil, [m])
        in
           if List.exists (fn x => x = c) forbiddenCids then
              SOME(inst) (* there is already an instantiation for c or one of its prefixes *)
           else if List.exists (fn p => List.exists (fn x => x = p) forbiddenPrefixes) prefixes then
              SOME(inst) (* there is already an instantiation for something with prefix c *)
           else if List.exists (fn d => M.sigIncluded(m,d)) inclInstDoms then
              SOME(inst) (* there is already an InclInst with domain d that includes the domain m of c *)
           else if List.exists (fn d => List.exists (fn e => M.sigIncluded(e, d)) otherDoms) inclInstDom then 
              SOME(inst) (* there is already an instantiation for a symbol included from a signature e that is included into the domain d of this InclInst *)
           else
              findClash'(insts, c :: forbiddenPrefixes, c :: prefixes @ forbiddenCids, 
                          inclInstDom @ inclInstDoms, otherDom @ otherDoms)
        end
  (* checks whether two instantiations in insts clash
     - return NONE if no clash
     - returns SOME c if an instantation for c is the first one leading to a clash
     a clash arises if there are instantiations for both
     - c and c, or
     - s and s.c
  *)
  fun findClash(insts) = findClash'(insts, nil, nil, nil, nil)

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

  (* checks the morphisms included into a structure or view
     A structure/view dom -> cod may include morphisms m_i : d_i -> com for signatures d_i included (M.Included _) into dom.
     If m_i is not given
      - in a view, applyMorph will assume the identity; therefore, we check that d_i is also be included into cod;
      - in a structure, nothing has to be checked; flattenDec will generate a structure with domain d_i anyway. 
     If there is a diamond situation with d included into d_1 and d_2, we check that the morphisms m_1 and m_2 agree on d. *)
  fun checkIncludes(dom : IDs.mid, cod : IDs.mid, mors : M.Morph list, inStructure : bool) =
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
      	           else if inStructure then () else raise Error("signature " ^ M.modFoldName from ^ " included into " ^ M.modFoldName dom ^
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
            of SOME inst => raise Error("multiple (possibly induced) instantiations for the same symbol; caused by instantiation: " ^
                                      Print.instToString inst)
             | NONE => ();
          val _ = checkIncludes(dom, cod, inclMorphsStr insts, true)
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
  fun checkSigIncl(si as M.SigIncl (m,_,_)) =
       if M.inSignature()
       then checkAncestors(m, M.currentMod())
       else raise Error("including signatures only allowed in signatures")

  (* checks well-typedness conditions for modules (called at the end of the module *)
  fun checkModEnd(m) = case M.modLookup m
     of M.SigDec _ => ()
      | M.ViewDec(_, _, dom, cod, _) =>
        let
          val _ = checkAncestors(dom, cod)
          val _ = checkIncludes(dom, cod, inclMorphsView m, false)
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
            (* return the morphism application if mor is applicable *) 
            | M.InclInst(i, _, dom, mor) => if M.sigIncluded(IDs.midOf c, dom) then SOME (applyMorph(cidToExp c, mor)) else getInst'(insts, c, q)
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
    flattenDec'(S, installConDec, installStrDec, NONE)
  and flattenDec'(S, installConDec, installStrDec, inclMapOpt) =
     let
     	val Str = M.structLookup S
     	val Name = M.strDecName Str
     	val Q = M.strDecQid Str
     	val Dom = M.strDecDom Str
     	(* holds the list of pairs (s',s) of original and induced inclusion/structure ids *)
     	val structMap : (IDs.cid * IDs.cid) list ref = ref nil
     	(* applies structMap to the first components of the pairs in q *)
     	fun applyStructMap(q: IDs.qid) = List.map (fn (x,y) => (#2 (valOf (List.find (fn z => #1 z = x) (!structMap))), 
     	                                                y)
     	                                          ) q
     	(* holds the list of pairs (d',s) of original inclusion domains and induced structure ids *)
     	val inclMap : (IDs.mid * IDs.cid) list ref = ref nil

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
                 if uni' = I.Type andalso checkStrict(defnew, typ)
                 (* return a ConDef if the input was a term-level ConDef and strictness is preserved *)
                 then I.ConDef(Name @ name', q, imp', defnew, typ, uni', ancestor defnew)
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
                | M.SymIncl(M.SigIncl(dom', _,_)) => (
                   (* If no inclMap is passed, all includes i' from dom' into Dom are elaborated recursively:
                      - a new structure s with domain dom' is created and flattened
                      - name', the name of dom', is used as an identifier for s  (dot-separated, without prefix, one string)
                      - inclMap maps each dom' to s
                      Since includes are subject to the identify-semantics, the recurisve flattening should not happen again when flattening s.
                      Instead, inclMap is passed so that the flattening of s can share the already-generated structures instead of generating new ones.
                   *)
                case inclMapOpt
                  of NONE =>
                   let
                      val i' = c'
                      val name' = M.modFoldName dom' 
                      val q = [(S, i')]
                      val s = case Str
                        of M.StrDec(_,_,_,insts,_,_) =>
                           let
                             val restrInsts = restrictInsts(insts, dom')
                           in
                             installStrDec (i', M.StrDec(Name @ [name'], q, dom', restrInsts, M.OpenDec nil, false))
                           end
                         | M.StrDef(_,_,_,def,_) => installStrDec (i', M.StrDef(Name @ [name'], q, dom', def, false))
                      val _ = structMap := (i',s) :: (! structMap)
                      val _ = inclMap := (dom', s) :: (! inclMap)
                      val _ = flattenDec'(s, installConDec, installStrDec, SOME (! inclMap))
                   in
                      ()
                   end
                 | SOME im =>
                    (* recursive flattening of the generated structures; just add an to M.structMap to realize the sharing *)
                    let val s = #2 (valOf (List.find (fn (x,_) => x = dom') im))
                        val _ = M.structMapAdd((S,c'),s)
                    in ()
                    end
                 )
                | M.SymMod _ => ()
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
                  | M.SymMod _ => ()
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