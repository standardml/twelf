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
  fun strDecName (StrDec(n, _, _, _)) = n
  fun strDecQid (StrDec(_, _, q, _)) = q
  fun strDecDomain (StrDec(_, _, m, _)) = m
  datatype SymDec = StrSym of StrDec | ConSym of I.ConDec
  (* a structure declaration instantiates a module with a list of assignments of expressions to qids *)
  exception UndefinedCid
  val symTable : I.ConDec QH.Table = QH.new(19999)
  val structTable : StrDec QH.Table = QH.new(999)
  val modTable : int IH.Table = IH.new(499)
  (* should be array since editing is necessary for every entry *)
    
  val nextMid = ref 0
  fun nextLid(m : IDs.mid) = valOf (IH.lookup(modTable)(m))
  fun incrLid(m : IDs.mid) = IH.insert(modTable)(m, nextLid(m) + 1)
    
  val scope : IDs.mid list ref = ref nil
  fun currentMod () = hd (! scope)
  fun inCurrent(l : IDs.lid) = IDs.newcid(currentMod(), l)
  fun sgnReset () = (QH.clear symTable; QH.clear structTable; IH.clear modTable)
    
  (* if conDecQid is nil, it should be replaced with lid; used in m2/prover.fun *)
  fun sgnAdd (m : IDs.mid, conDec : I.ConDec) =
    let
      val c = IDs.newcid(m, nextLid(m))
    in
      QH.insert(symTable)(c, conDec);
      incrLid(m);
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
	if l = nextLid(m) then () else (f (IDs.newcid(m,l)); doRest(IDs.nextLid(l)))
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
  fun sgnAppC (f) = sgnApp(currentMod(), f)
    
  fun structAdd (m : IDs.mid, strDec : StrDec) =
    let
      val c = IDs.newcid(m, nextLid(m))
    in
      QH.insert(structTable)(c, strDec);
      incrLid(m);
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

  fun hack (c, conDec : I.ConDec) =
    QH.insert(symTable)(c, conDec)
end

structure ModSyn =
  ModSyn (structure IntSyn = IntSyn);

