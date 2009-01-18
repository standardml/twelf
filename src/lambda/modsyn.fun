(* Syntax for elaborated modules *)
(* Author: Florian Rabe *)

functor ModSyn (structure IntSyn : INTSYN)
  : MODSYN =
struct
  structure QH = CidHashTable
  structure IH = IntHashTable
  structure I = IntSyn  
  
  exception Error of string

  datatype Morph = MorStr of IDs.cid
  datatype SymInst = ConInst of IDs.cid * I.Exp | StrInst of IDs.cid * Morph
  datatype StrDec = StrDec of string * IDs.qid * IDs.mid * (SymInst list)

  datatype SymDec = StrSym of StrDec | ConSym of I.ConDec

  fun strDecName (StrDec(n, _, _, _)) = n
  fun strDecQid (StrDec(_, _, q, _)) = q
  fun strDecDomain (StrDec(_, _, m, _)) = m

  exception UndefinedCid
    (* Invariants *)
    (* Constant declarations are all well-typed *)
    (* Constant declarations are stored in beta-normal form *)
    (* All definitions are strict in all their arguments *)
    (* If Const(cid) is valid, then sgnArray(cid) = ConDec _ *)
    (* If Def(cid) is valid, then sgnArray(cid) = ConDef _ *)

  val symTable : I.ConDec QH.Table = QH.new(19999)
  val structTable : StrDec QH.Table = QH.new(999)
  (* should be array since editing is necessary for every entry *)
  val modTable : IDs.lid IH.Table = IH.new(499)
 
  val scope : IDs.mid list ref = ref nil

  fun currentMod () = hd (! scope)
  fun inCurrent(l : IDs.lid) = IDs.newcid(currentMod(), l)
    
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

  fun modClose() = ()
    
  fun sgnReset () = (
    QH.clear symTable; 
    QH.clear structTable;
    IH.clear modTable;
    modOpen();
    ()
  )
  
  (* if conDecQid is nil, it should be replaced with lid; used in m2/prover.fun *)
  fun sgnAdd (m : IDs.mid, conDec : I.ConDec) =
    let
      val c = IDs.newcid(m, getNextLid(m))
    in
      QH.insert(symTable)(c, conDec);
      incrNextLid(m);
      c
    end
  
  fun sgnAddC (conDec : I.ConDec) = sgnAdd(currentMod(), conDec)
    
  fun sgnLookup (c : IDs.cid) = case QH.lookup(symTable)(c)
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
    in
      QH.insert(structTable)(c, strDec);
      incrNextLid(m);
      c
    end      
  fun structAddC (strDec : StrDec) = structAdd(currentMod(), strDec)
    
  fun structLookup(c : IDs.cid) = case QH.lookup(structTable)(c)
    of SOME d => d
  | NONE => raise UndefinedCid
  val structLookupC = structLookup o inCurrent

  fun symLookup(c : IDs.cid) =
    StrSym(structLookup c)
    handle UndefinedCid => ConSym(sgnLookup c)

  (* Convenience methods to access constant declarations by id *)
  fun constDef (d) =
      (case sgnLookup (d)
	 of I.ConDef(_, _, _, U,_, _, _) => U
	  | I.AbbrevDef (_, _, _, U,_, _) => U)
  fun constType (c) = I.conDecType (sgnLookup c)
  fun constImp (c) = I.conDecImp (sgnLookup c)
  fun constUni (c) = I.conDecUni (sgnLookup c)
  fun constBlock (c) = I.conDecBlock (sgnLookup c)
  fun constStatus (c) =
      (case sgnLookup (c)
	 of I.ConDec (_, _, _, status, _, _) => status
          | _ => I.Normal)
  
  (* These might also be in IntSyn.fun. But they must be here because they need to look up and expand type definitions. *)

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

  (* used for Flit *)
  fun hack (c, conDec : I.ConDec) =
    QH.insert(symTable)(c, conDec)
end

structure ModSyn =
  ModSyn (structure IntSyn = IntSyn);

