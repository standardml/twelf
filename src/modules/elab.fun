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
  exception UndefinedMorph of IDs.mid * IDs.cid   (* raised if partially defined view cannot be applied *)
  exception FixMe                                 (* raised for unimplemented cases *)


  (********************** Module level type checking **********************)

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

  (* computes domain of a morphism without checking composability *)
  fun domain(mor : M.Morph) : IDs.mid = case mor
    of M.MorView m => let val M.ViewDec(_, _, dom, _, _) = M.modLookup m in dom end
     | M.MorStr s => M.strDecDom (M.structLookup s)
     | M.MorComp(m,_) => domain m
  
  (* computes codomain of a morphism without checking composability *)
  fun codomain(mor : M.Morph) : IDs.mid = case mor
    of M.MorView m => let val M.ViewDec(_, _, _, cod, _) = M.modLookup m in cod end
     | M.MorStr s => IDs.midOf(s)
     | M.MorComp(_,m) => codomain m
  
  (* reconstructs the type, i.e., domain and codomain of a morphism and checks whether it is well-formed *)
  (* composibility is co-/contravariant with respect to inclusions *)
  fun reconMorph(M.MorComp(mor1,mor2)) =
        let
           val (d1,c1,m1) = reconMorph mor1
           val (d2,c2,m2) = reconMorph mor2
        in
           if M.sigInclCheck(c1,d2)
           then (d1,c2, M.MorComp(m1,m2))
           else case M.implicitLookup(c1, d2)
              of SOME m => (d1, c2, M.MorComp(m1, M.MorComp(m, m2)))
               | NONE => raise Error("morphisms not composable")
        end
    | reconMorph(M.MorStr s) = ((M.strDecDom (M.structLookup s), IDs.midOf(s), M.MorStr s)
                              handle M.UndefinedCid _ => raise Error("non-structure symbol reference in morphism"))
    | reconMorph(M.MorView m) =
        let
           val M.ViewDec(_, _, dom, cod, _) = M.modLookup m
                                        handle M.UndefinedMid _ => raise Error("non-view module reference in morphism")
        in
           (dom, cod, M.MorView m)
        end

  (* checks the judgment |- mor : dom -> cod (co-/contravariant with respect to inclusions)
     returns reconstructed morphism *)
  and checkMorph(mor, dom, cod) =
     let
     	val (d,c, mor2) = reconMorph mor
     	val inclBefore = M.sigInclCheck(dom,d)
        val implBefore = if inclBefore then NONE else M.implicitLookup(dom, d)
        val inclAfter  = M.sigInclCheck(c,cod)
        val implAfter  = if inclAfter then NONE else M.implicitLookup(c, cod)
     in
     	case (inclBefore, implBefore, inclAfter, implAfter)
     	  of (true, _, true, _) => mor2
     	   | (true, _, false, SOME m) => M.MorComp(mor2, m)
     	   | (false, SOME m, true, _) => M.MorComp(m, mor2)
     	   | (false, SOME m, false, SOME n) => M.MorComp(m, M.MorComp(mor2, n))
           | _ => raise Error("morphism does not have expected type")
     end

  (* checks equality of two paths in the signature graphs *)
  and equalMorph(mor1, mor2) = (mor1 = mor2)
  
  (* turns a morphism into a (possibly empty) path in the signature graph, i.e., a list of links, 
     pre: mor is well-formed, newdom is included into domain(mor)
     post: restrictMorph(mor, newdom) of type M.Morph list
       is equal to mor and consists of only MorView _ or MorStr _ such that
       - definitions are expanded
       - the domain of the first is newdom
       - the domain of each is the codomain of the predecessor (i.e., includes are expanded)
   *)
  and restrictMorph(M.MorComp(mor1,mor2), newdom) =
      let val mor1l = restrictMorph(mor1, newdom)
          val cod = if mor1l = nil then newdom else codomain(List.last mor1l)
          val mor2l = restrictMorph(mor2, cod)
      in
      	  mor1l @ mor2l
      end
    | restrictMorph(M.MorStr c, newdom) = (case M.structLookup c
                              of M.StrDef(_,_,_,mor,_) => restrictMorph (mor, newdom)
                               | M.StrDec _ => restrictMorph1(M.MorStr c, newdom)
                            )
    | restrictMorph(M.MorView m, newdom) = restrictMorph1(M.MorView m, newdom)
  (* as restrictMorph, but additionally
     pre: mor is a declared link
   *)
  and restrictMorph1(mor, newdom) = if domain(mor) = newdom then [mor] else
     let val incls = case mor
                    of M.MorStr c => (fn M.StrDec(_,_,_,x,_,_,_) => x) (M.structLookup c)
                     | M.MorView m => M.modInclLookup m
     in case linkInclGet(incls, newdom)
       of nil => nil (* the identity path *)
        | m :: _ => restrictMorph (m, newdom)
     end

  and checkSymInst(ci as M.ConInst(con, _, term)) =
      let
     	val v = M.currentMod()
     	val typ = M.constType con
     	val expTyp = applyMorph(typ, M.MorView v)
        (* make sure there are no clashes, i.e., symLookup must be undefined *)
        val _ = ( M.symLookup(v, IDs.lidOf con);
                  raise Error("instantiation for " ^ M.symFoldName con ^ " already defined")
                ) handle M.UndefinedCid _ => ()
     in
     	if checkType(term, expTyp)
     	then ci
        else raise Error("type mismatch")
     end
    | checkSymInst(M.StrInst(str, org, mor)) =
     let
     	val expDom = M.strDecDom (M.structLookup str)
     	val m = checkMorph(mor, expDom, M.currentTargetSig())
     in
     	M.StrInst(str, org, m)
     end

  (* auxiliary function of findClash
     if s is in forbiddenPrefixes, instantiations of s.c are forbidden
     if c is in forbiddenCids, instantiations of c are forbidden
  *)
  and findClash'(nil, _, _) = NONE
    | findClash'(inst :: insts, forbiddenPrefixes, forbiddenCids) =
        let
           val c = M.symInstCid inst
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
  and findClash(insts) = findClash'(insts, nil, nil)
      
  (* goes through morphism inclusions, returns all with domain "from" *)
  and linkInclGet(incls, from) =
     List.mapPartial (fn M.ViewIncl mor => if M.sigInclCheck(from, domain mor) then SOME mor else NONE) incls
 
  (* auxiliary functions that checks whether the ancestors of a link (structure, view, or include) are compatible *)
  and checkAncestors(dom, cod) =
    let
       val domPar = M.modParent dom
       val codPar = M.modParent cod
       val _ = if List.exists (fn (m,_) => m = dom) codPar
               then raise Error("domain of link may not be ancestor of codomain")
               else ()
       val _ = if List.all (fn (m,l) => m = cod orelse List.exists (fn (m',l') => m = m' andalso l <= l') codPar) domPar
               then ()
               else raise Error("all ancestors of the domain of a link must be ancestors of the codomain")
               (* The above condition implies that views between sister signatures
                  are only permitted if the domain can access at most as many constants of the parent as the codomain. *)
    in
       ()
    end

  (* all includes of the domain must be included or translated into the codomain
     if there are multiple translations, they must be equal *)
  and checkIncludesOfDomain(dom : IDs.mid, cod : IDs.mid, incls : M.ModIncl list) =
        List.map
      	  (fn from =>
      	    case linkInclGet(incls, from)
      	      of nil => if M.sigInclCheck(from,cod)
      	                 then ()
      	                 else raise Error("signature " ^ M.modFoldName from ^ " included into " ^ M.modFoldName dom ^
                                          " but not into " ^ M.modFoldName cod)
               | l => let val hd :: tl = List.map (fn x => restrictMorph(x, from)) l
                      in
                      	case List.find (fn x => not(equalMorph(x, hd))) tl
                      	  of NONE => ()
                           | SOME (mor :: _) => raise Error("conflicting translations for included signature " ^
                               M.modFoldName (domain mor) ^ " (implementation restriction: equality of morphisms only checked up to associativity and definition expansion)")
                      end
          )
          (M.sigInclLookupTrans dom)

   (* checks domain and codomain of a morphism included into a link from Dom to Cod; returns reconstructed morphism *)
   and checkIncludeInLink(Dom, Cod, mor) =
      let
       	 val (dom, cod, newmor) = reconMorph mor
         val _ = if M.sigInclCheck(dom, Dom)
                 then ()
                 else raise Error("included morphism has bad domain: " ^ M.modFoldName dom)
         val _ = if M.sigInclCheck(cod, Cod)
       	         then ()
       	         else raise Error("included morphism has bad codomain: " ^ M.modFoldName cod)
      in
      	 newmor
      end

  (* checks simple well-typedness condition for includes; returns reconstructred include *)
  and checkModIncl(si as M.SigIncl (m,_)) =
       if M.inSignature()
       then (checkAncestors(m, M.currentMod()); si)
       else raise Error("including signatures only allowed in signatures")
    | checkModIncl(M.ViewIncl mor) =
       let
       	  val v = M.currentMod()
       	  val M.ViewDec(_, _, Dom, Cod, _) =
       	     if M.inSignature()
       	     then raise Error("including morphisms only allowed in links")
       	     else M.modLookup v
       	  val newmor = checkIncludeInLink(Dom, Cod, mor)
       	in
       	   M.ViewIncl newmor
       	end

  (* checks simple well-typedness conditions for structure declarations
     does not check:
     - all instantiations instantiate domain symbols with codomain expressions
       already checked during parsing/reconstruction
     - all instantiations are well-typed and preserve equalities
       will be checked during flattening
     postcondition: getInst yields all information that is needed to check the latter during flattening
  *)
  and checkStrDec(M.StrDec(n, q, dom, incls, insts, opens, impls)) =
       let
       	  val cod = M.currentMod()
          val _ = checkAncestors(dom, cod);
          val newincls = List.map (fn M.ViewIncl mor => M.ViewIncl(checkIncludeInLink(dom, cod, mor))) incls;
          val _ = checkIncludesOfDomain(dom, cod, newincls);
          val _ = case findClash insts
            of SOME c => raise Error("multiple (possibly induced) instantiations for " ^
                                      M.symFoldName c ^ " in structure declaration")
             | NONE => ();
          val newinsts = List.map (fn si as M.StrInst _ => checkSymInst si | ci => ci) insts;
       in
          M.StrDec(n, q, dom, newincls, newinsts, opens, impls)
       end
    | checkStrDec(M.StrDef(n, q, dom, mor, i)) =
        let val cod = M.currentMod()
            val _ = checkAncestors(dom, cod)
            val newmor = checkMorph(mor, dom, cod)
        in 
           M.StrDef(n, q, dom, newmor, i)
        end

  (* checks well-typedness conditions for modules (called at the beginning of the module *)
  and checkModBegin(_) = ()
  (* checks well-typedness conditions for modules (called at the end of the module *)
  and checkModEnd(m) =
       if M.inSignature() then () else
       let
          val M.ViewDec(_, _, dom, cod, _) = M.modLookup m
          val _ = checkAncestors(dom, cod)
          val _ = checkIncludesOfDomain(dom, cod, M.modInclLookup m)
          (* check totality of view: every undefined constant id of dom must have an instantiation in m *)
          (* @CS what about block and skodec? *)
          fun checkDefined(c' : IDs.cid) = case M.symLookup c'
              of M.SymCon (I.ConDec _) => ((M.symLookup(m, IDs.lidOf c') ; ())
                 handle M.UndefinedCid _ => raise Error("view not total: missing instatiation for " ^ M.symFoldName c'))
               | _ => ()
       in
          M.sgnApp(dom, checkDefined)
       end


 (********************** Semantics of the module system **********************)
  (* auxiliary methods to get Exps from cids *)
  and headToExp h = I.Root(h, I.Nil)
  and cidToExp c = (case (M.sgnLookup c)
		      of (I.ConDec _) => headToExp(I.Const c)
		       | (I.ConDef _) => headToExp (I.Def c)
		       | (I.AbbrevDef _) => headToExp (I.NSDef c))
  (* pre: U is well-formed term over the domain of mor
     pre: mor is well-formed (all implicit coercions filled in)
     post: U is well-formed term over the codomain of mor
   *)
  and applyMorph(U, mor) =
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
          | A(I.FgnExp(cs, F)) = raise FixMe
          | A(I.NVar n) = I.NVar n
        and AHead(I.BVar k) = headToExp(I.BVar k)
          | AHead(I.Const c) = ACid c            (* apply morphism to constant *)
          | AHead(I.Proj(b,k)) = headToExp(I.Proj (ABlock b, k))
          | AHead(I.Skonst c) = ACid c           (* apply morphism to constant *)
          | AHead(I.Def d) = A (M.constDef d)    (* expand definition *)
          | AHead(I.NSDef d) = A (M.constDef d)  (* expand definition *)
          | AHead(I.FVar(x, U, s)) = headToExp(I.FVar(x, A U, ASub s))
          | AHead(I.FgnConst(cs, condec)) = raise FixMe
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
              case (mor, m = dom)
                (* apply morphism by applying structMapLookup *)
                of (M.MorStr(s), true) => cidToExp(valOf(M.structMapLookup (s,c)))    (* get the cid to which s maps c *)
                (* apply morphism by looking up instantiation of view *)
                 | (M.MorView(v), true) => (
                     let val ModSyn.ConInst(_, _, exp) = ModSyn.conInstLookup(v, IDs.lidOf(c))
                     in exp
                     end
                     handle ModSyn.UndefinedCid _ => raise UndefinedMorph(v,c)
                   )
                 (* apply composed morphisms separately *)
                 | (M.MorComp(mor1, mor2), _) => applyMorph(applyMorph(cidToExp(c), mor1), mor2)
                 (* included constants are mapped to themselves unless an applicable morphism is included *)
                 | (link, false) =>
                     let fun byIncludes(incls) = case linkInclGet(incls, m)
              	             of newmor :: _ => applyMorph(cidToExp(c), newmor)  (* apply included morphism *)
              	              | nil => cidToExp c                               (* default to identity *)
                     in case link
                          of M.MorView v => byIncludes(M.modInclLookup v)
                           | M.MorStr s => (case M.structLookup s
                               of M.StrDef(_, _, _, newmor, _) => applyMorph(cidToExp(c), newmor) (* expand link definition *) 
                                | M.StrDec(_, _, _, incls, _, _, _) => byIncludes(incls)
                             )
              	     end
           end
     in
     	A U
     end
  
  (* auxiliary function of getInst, its first argument is a list of instantiations *)
  and getInst'(nil, c, q) = NONE
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
      )
  (* finds an instantiation for cid c having qids q in a structure declaration
     this finds both explicit instantiations (c := e) and induced instantiations (s := mor in case c = s.c')
     in StrDefs, the instantiation is obtained by applying the definition of the structure to c
  *)
  and getInst(M.StrDec(_,_,_,_, insts, _, _), c, q) = getInst'(insts, c, q)
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
  and flattenDec(S : IDs.cid, installConDec : IDs.cid * I.ConDec -> IDs.cid, installStrDec : IDs.cid * M.StrDec -> IDs.cid) =
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
           | translateConDec(_, I.SkoDec(_, _, _, _, _)) = raise FixMe
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
     in
     	(* calls flatten1 on all declarations of the instantiated signature (including generated ones) *)
     	M.sgnApp(Dom, flatten1)
     end

  and flattenInst(instID : IDs.cid, installInst : M.SymInst -> IDs.cid) =
     let
        val viewID = IDs.midOf instID
        val M.SymStrInst(M.StrInst(s, _, mor)) = M.symLookup instID
        val (dom, _, _) = reconMorph mor
        fun flatten1(c' : IDs.cid) =
           let 
              val c = valOf (M.structMapLookup(s,c'))
              val _ = case M.symLookup c'
                 of M.SymCon _ =>
                   let
                      val defCod = normalize (applyMorph(cidToExp c', mor))
                      val typDomTrans = normalize(applyMorph(M.constType c, M.MorView viewID))
                      val _ = if checkType(defCod, typDomTrans)
                              then ()
                              else raise Error("type mismatch in induced instantiation of " ^ M.symFoldName c)
                      val _ = case M.constDefOpt c
                                of NONE => ()
                                 | SOME defDom =>
                                   if checkEqual(applyMorph(defDom, M.MorView viewID), defCod)
                                   then ()
                                   else defInstClash(defDom, defCod, applyMorph(defDom, M.MorView viewID),
                                                     "definition/instantiation clash for " ^ M.symFoldName c)
                   in
                      installInst(M.ConInst(c, SOME instID, defCod))
                   end
                  | M.SymStr _ => installInst(M.StrInst(c, SOME instID, M.MorComp(M.MorStr c', mor)))
           in
              () 
           end
     in
        M.sgnApp(dom, flatten1)
     end
end