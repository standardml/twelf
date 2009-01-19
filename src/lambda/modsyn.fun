(* Syntax and semantics of the module system, also encapsulation of the state of modular LF *)
(* Author: Florian Rabe *)

(* The datatypes and interface methods are well-documented in the declaration of MODSYN. *)
functor ModSyn (structure IntSyn : INTSYN)
  : MODSYN =
struct
  structure CH = CidHashTable
  structure CCH = HashTable (type key' = IDs.cid * IDs.cid
             val hash = fn (x,y) => 100 * (IDs.cidhash x) + (IDs.cidhash y)
             val eq = (op =));
  structure IH = IntHashTable
  structure I = IntSyn

  exception Error of string

  datatype Morph = MorStr of IDs.cid | MorView of IDs.mid | MorComp of Morph * Morph
  datatype SymInst = ConInst of IDs.cid * I.Exp | StrInst of IDs.cid * Morph
  datatype StrDec = StrDec of string list * IDs.qid * IDs.mid * (SymInst list)
                  | StrDef of string list * IDs.qid * IDs.mid * Morph
  datatype SigDec = SigDec of string list
  datatype ViewDec = ViewDec of string list * IDs.mid * IDs.mid

  (* unifies constant and structure declarations *)
  datatype SymDec = SymCon of I.ConDec | SymStr of StrDec

  fun strDecName (StrDec(n, _, _, _)) = n
    | strDecName (StrDef(n, _, _, _)) = n
  fun strDecQid (StrDec(_, q, _, _)) = q
    | strDecQid (StrDef(_, q, _, _)) = q
  fun strDecDom (StrDec(_, _, m, _)) = m
    | strDecDom (StrDef(_, _, m, _)) = m

  fun symInstCid(ConInst(c, _)) = c
    | symInstCid(StrInst(c, _)) = c

  exception UndefinedCid
  exception NoOpenModule

    (* Invariants *)
    (* Constant declarations are all well-typed *)
    (* Constant declarations are stored in beta-normal form *)
    (* All definitions are strict in all their arguments *)
    (* If Const(cid) is valid, then sgnArray(cid) = ConDec _ *)
    (* If Def(cid) is valid, then sgnArray(cid) = ConDef _ *)

  val symTable : I.ConDec CH.Table = CH.new(19999)
  val structTable : StrDec CH.Table = CH.new(999)
  (* should be array since editing is necessary for every entry *)
  val modTable : IDs.lid IH.Table = IH.new(499)
  val structMapTable : IDs.cid CCH.Table = CCH.new(19999)
   
  (* management of the currently opened modules *)
  val scope : IDs.mid list ref = ref nil
  fun currentMod () = hd (! scope)
  fun inCurrent(l : IDs.lid) = IDs.newcid(currentMod(), l)

  (* maintenance of next available mids and lids *)    
  val nextMid : IDs.mid ref = ref 0
  fun incrNextMid() = nextMid := ! nextMid + 1
  val getNextLid = valOf o (IH.lookup modTable)
  val setNextLid = IH.insert modTable
  fun incrNextLid(m : IDs.mid) = setNextLid(m, IDs.nextLid(getNextLid m))

  fun modOpen() =
     let
        val m = ! nextMid
        val _ = incrNextMid
    	val _ = setNextLid(m,0)
        val _ = scope := m :: (! scope)
     in
     	m
     end

  fun modClose() =
    if (List.length (! scope) < 1)
       then
       	  raise NoOpenModule
       else
       	  scope := tl (! scope)
    
  fun reset () = (
    CH.clear symTable; 
    CH.clear structTable;
    IH.clear modTable;
    modOpen();
    ()
  )
  
  fun sgnAdd (m : IDs.mid, conDec : I.ConDec) =
    let
      val c = IDs.newcid(m, getNextLid(m))
      val q = I.conDecQid conDec
    in
      CH.insert(symTable)(c, conDec);
      incrNextLid(m);
      (* q = [(s_1,c_1),...,(s_n,c_n)] where every s_i maps c_i to c *)
      List.map (fn sc => CCH.insert structMapTable (sc, c)) q;
      c
    end
  
  fun sgnAddC (conDec : I.ConDec) = sgnAdd(currentMod(), conDec)
    
  fun sgnLookup (c : IDs.cid) = case CH.lookup(symTable)(c)
    of SOME d => d
  | NONE => raise UndefinedCid
  val sgnLookupC = sgnLookup o inCurrent
    
  fun sgnApp(m : IDs.mid, f : IDs.cid -> unit) =
    let
      fun doRest(l) = 
	if l = getNextLid(m) then () else (f (IDs.newcid(m,l)); doRest(IDs.nextLid(l)))
    in
      doRest(IDs.firstLid())
    end
  fun sgnAppC (f) = sgnApp(currentMod(), f)

  fun modApp(f : IDs.mid -> unit) =
    let
      fun doRest(m) = 
	if m = (! nextMid) then () else ((f m); doRest(IDs.nextMid(m)))
    in
      doRest(IDs.firstLid())
    end
    
  fun structAdd (m : IDs.mid, strDec : StrDec) =
    let
      val c = IDs.newcid(m, getNextLid(m))
      val _ = incrNextLid(m);
      val _ = CH.insert(structTable)(c, strDec)
    in
      c
    end      
  fun structAddC (strDec : StrDec) = structAdd(currentMod(), strDec)

  fun structLookup(c : IDs.cid) = case CH.lookup(structTable)(c)
    of SOME d => d
  | NONE => raise UndefinedCid
  val structLookupC = structLookup o inCurrent

  fun symLookup(c : IDs.cid) =
    SymStr(structLookup c)
    handle UndefinedCid => SymCon(sgnLookup c)

  fun constDefOpt (d) =
      (case sgnLookup (d)
	 of I.ConDef(_, _, _, U,_, _, _) => SOME U
	  | I.AbbrevDef (_, _, _, U,_, _) => SOME U
	  | _ => NONE)
  val constDef = valOf o constDefOpt
  fun constType (c) = I.conDecType (sgnLookup c)
  fun constImp (c) = I.conDecImp (sgnLookup c)
  fun constUni (c) = I.conDecUni (sgnLookup c)
  fun constBlock (c) = I.conDecBlock (sgnLookup c)
  fun constStatus (c) =
      (case sgnLookup (c)
	 of I.ConDec (_, _, _, status, _, _) => status
          | _ => I.Normal)
  
  fun headToExp h = I.Root(h, I.Nil)
  fun cidToExp c = headToExp(I.Const c)
  exception FixMe (* @CS: search for this exception, only temporary to make stuff compile *)
  fun applyMorph(U, mor) =
     let
     	fun A(I.Uni L) = I.Uni L
     	  | A(I.Pi((D, P), V)) = I.Pi((ADec D, P), A V)
     	  | A(I.Root(H, S)) = I.Redex(AHead H, ASpine S)
     	  | A(I.Redex(U, S)) = I.Redex(A U, ASpine S)
     	  | A(I.Lam(D, U)) = I.Lam(ADec D, A U)
     	  | A(I.EVar(E, C, U, Constr)) = raise FixMe
          | A(I.EClo(U,s)) = I.EClo(A U, ASub s)
          | A(I.AVar(I)) = raise FixMe
          | A(I.FgnExp(cs, F)) = raise FixMe
          | A(I.NVar n) = I.NVar n
        and AHead(I.BVar k) = headToExp(I.BVar k)
          | AHead(I.Const c) = ACid c          (* apply morphism to constant *)
          | AHead(I.Proj(b,k)) = headToExp(I.Proj (ABlock b, k))
          | AHead(I.Skonst c) = ACid c         (* apply morphism to constant *)
          | AHead(I.Def d) = A (constDef d)    (* expand definition *)
          | AHead(I.NSDef d) = A (constDef d)  (* expand definition *)
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
          | ADec(I.BDec(v,(l,s))) = I.BDec(v,(raise FixMe, ASub s))
          | ADec(I.ADec(v,d)) = I.ADec(v,d)
          | ADec(I.NDec v) = I.NDec v
        and ABlock(I.Bidx i) = I.Bidx i
          | ABlock(I.LVar(b,s,(c,s'))) = raise FixMe
          | ABlock(I.Inst l) = I.Inst (List.map A l)
        and AConstr(I.Solved) = I.Solved
          | AConstr(I.Eqn(G, U1, U2)) = raise FixMe
          | AConstr(I.FgnCnstr(cs, fgnC)) = I.FgnCnstr(cs, fgnC)
        and ACid(c) =
           case mor
             of MorStr(s) => cidToExp(valOf(CCH.lookup structMapTable (s,c)))  (* get the cid to which s maps c *)
              | MorView(m) => raise FixMe                                      (* views not implemented yet *)
              | MorComp(mor1, mor2) => applyMorph(applyMorph(cidToExp(c), mor1), mor2)
     in
     	A U
     end
  
  (* auxiliary function of getInst, its first argument is a list of instantiations *)
  fun getInst'(nil, c, q) = NONE
    | getInst'(inst :: insts, c, q) = (
        case inst
           (* if c is instantiated directly, return its instantiation *)
           of ConInst(c, e) => SOME e
           (* if c can be addressed as c' imported via s, and if s is instantiated with mor,
              return the application of mor to c' *)
            | StrInst(s, mor) => (
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
  fun getInst(StrDec(_,_,_,insts), c, q) = getInst'(insts, c, q)
    | getInst(StrDef(_,_,_,mor), c, _) = SOME (applyMorph(cidToExp c, mor))
  
  (* auxiliary function of findClash
     if s is in forbiddenPrefixes, instantiations of s.c are forbidden
     if c is in forbiddenCids, instantiations of c are forbidden
  *)
  fun findClash'(nil, _, _) = NONE
    | findClash'(inst :: insts, forbiddenPrefixes, forbiddenCids) =
        let
           val c = symInstCid inst
        in
           (* check whether c is in the list of cids of forbidden cids *)
           if List.exists (fn x => x = c) forbiddenCids
           then SOME(c)
           else
              let
              	 (* get the list of proper prefixes of c *)
                 val prefixes = List.map #1 (I.conDecQid (sgnLookup c))
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

  (* Note: This function can be left unchanged if this code is reused for a different internal syntax
     except for the local function translateConDec.
     It would be nicer to put translateConDec on toplevel, but that would be less efficient. *)
  fun flatten(c : IDs.cid, installConDec : I.ConDec -> IDs.cid, installStrDec : StrDec -> IDs.cid) =
     let
     	val str = structLookup c
     	val name = strDecName str
     	val q = strDecQid str
     	val dom = strDecDom str
     	val structMap : (IDs.cid -> IDs.cid) ref = ref (fn x => x)
        fun translateConDec(c', I.ConDec(name', q', imp', stat', typ', uni')) =
              let
                 val typ = applyMorph(typ', MorStr(c))
                 val tq = (c, c') :: List.map (fn (x,y) => ((! structMap) x, y)) q'
              in
                 case getInst(str, c', q')
                   of SOME def =>
                      I.AbbrevDef(name @ name', tq, imp', typ, def, uni') (* @CS: can this be a ConDef? *)
                    | NONE =>
                      I.ConDec(name @ name', tq, imp', stat', typ, uni')
              end
          | translateConDec(c', I.ConDef(name', q', imp', typ', def', uni', anc')) =
              let
                 val typ = applyMorph(typ', MorStr(c))
                 val def = applyMorph(def', MorStr(c))
                 val tq = (c, c') :: List.map (fn (x,y) => ((! structMap) x, y)) q'
              in
                 case getInst(str, c', q')
                   (* @CS: can those AbbrevDefs be ConDefs? *)
                   of SOME def =>
                      (* @FR: check def = def' *)
                      I.AbbrevDef(name @ name', tq, imp', typ, def, uni')
                    | NONE =>
                      I.AbbrevDef(name @ name', tq, imp', typ, applyMorph(def', MorStr(c)), uni')
              end
     	fun flatten1(c' : IDs.cid) =
     	   case symLookup c'
              of SymCon(con') => (
                   installConDec (translateConDec(c', con'));
                   ()
                 )
               | SymStr(str') =>
                let
                   val name' = strDecName str'
                   val q' = strDecQid str'
                   val dom' = strDecDom str'
                   val tq' = (c, c') :: List.map (fn (x,y) => ((! structMap) x, y)) q'
                   val tc' = installStrDec (StrDef(name @ name', tq', dom', MorComp(MorStr(c'), MorStr(c))))
                   val _ = structMap := (fn x => if x = c' then tc' else (! structMap) x)
                in
                   ()
                end
     in
     	sgnApp(dom, flatten1)
     end

  fun ancestor' (NONE) = I.Anc(NONE, 0, NONE)
    | ancestor' (SOME(I.Const(c))) = I.Anc(SOME(c), 1, SOME(c))
    | ancestor' (SOME(I.Def(d))) =
      (case sgnLookup(d)
	 of I.ConDef(_, _, _, _, _, _, I.Anc(_, height, cOpt))
            => I.Anc(SOME(d), height+1, cOpt))
    | ancestor' (SOME _) = (* FgnConst possible, BVar impossible by strictness *)
      I.Anc(NONE, 0, NONE)
  (* ancestor(U) = ancestor info for d = U *)
  fun ancestor (U) = ancestor' (I.headOpt U)

  (* defAncestor(d) = ancestor of d, d must be defined *)
  fun defAncestor (d) =
      (case sgnLookup(d)
	 of I.ConDef(_, _, _, _, _, _, anc) => anc)

  (* targetFamOpt (V) = SOME(cid) or NONE
     where cid is the type family of the atomic target type of V,
     NONE if V is a kind or object or have variable type.
     Does expand type definitions.
  *)
  fun targetFamOpt (I.Root (I.Const(c), _)) = SOME(c)
    | targetFamOpt (I.Pi(_, V)) = targetFamOpt V
    | targetFamOpt (I.Root (I.Def(c), _)) = targetFamOpt (constDef c)
    | targetFamOpt (I.Redex (V, S)) = targetFamOpt V
    | targetFamOpt (I.Lam (_, V)) = targetFamOpt V
    | targetFamOpt (I.EVar (ref (SOME(V)),_,_,_)) = targetFamOpt V
    | targetFamOpt (I.EClo (V, s)) = targetFamOpt V
    | targetFamOpt _ = NONE
      (* Root(Bvar _, _), Root(FVar _, _), Root(FgnConst _, _),
         EVar(ref NONE,..), Uni, FgnExp _
      *)
      (* Root(Skonst _, _) can't occur *)
  (* targetFam (A) = a
     as in targetFamOpt, except V must be a valid type
  *)
  fun targetFam (A) = valOf (targetFamOpt A)

  (* was used only by Flit, probably violates invariants
  fun rename (c, conDec : I.ConDec) =
    CH.insert(symTable)(c, conDec)
   *)
end (* functor ModSyn *)


(* ModSyn is instantiated with IntSyn right away. Both are visible globally. *)
structure ModSyn =
  ModSyn (structure IntSyn = IntSyn);

