(* Syntax and semantics of the module system, also encapsulation of the state of modular LF *)
(* Author: Florian Rabe *)
(* The datatypes and interface methods are documented in MODSYN. *)

functor ModSyn (structure IntSyn : INTSYN)
  : MODSYN =
struct
  structure CH = CidHashTable
  structure CCH = HashTable (type key' = IDs.cid * IDs.cid
             val hash = fn (x,y) => 100 * (IDs.cidhash x) + (IDs.cidhash y)
             val eq = (op =));
  structure MH = MidHashTable
  structure I = IntSyn

  exception Error of string
  exception UndefinedCid of IDs.cid
  exception UndefinedMid of IDs.mid

  datatype Morph = MorStr of IDs.cid | MorView of IDs.mid | MorId of IDs.mid | MorComp of Morph * Morph
  datatype Rel = Rel of IDs.mid | RelComp of Morph * Rel
  datatype SymInst = ConInst of IDs.cid * (IDs.cid option) * I.Exp | StrInst of IDs.cid * (IDs.cid option) * Morph
                   | InclInst of IDs.cid * (IDs.cid option) * Morph
  datatype SymCase = ConCase of IDs.cid * (IDs.cid option) * I.Exp | StrCase of IDs.cid * (IDs.cid option) * Rel
                   | InclCase of IDs.cid * (IDs.cid option) * Rel
  datatype OpenDec = OpenDec of (IDs.cid * string) list
  datatype StrDec = StrDec of string list * IDs.qid * IDs.mid * (SymInst list) * OpenDec * bool
                  | StrDef of string list * IDs.qid * IDs.mid * Morph * bool
  datatype SigIncl = SigIncl of IDs.mid * OpenDec
  datatype ModDec = SigDec of string * string list
                  | ViewDec of string * string list * IDs.mid * IDs.mid * bool
                  | RelDec of string * string list * IDs.mid * IDs.mid * (Morph list)

  datatype Read = ReadFile of string

  (* unifies all declarations that can occur in a module *)
  datatype Declaration = SymMod of IDs.mid * ModDec
                       | SymCon of I.ConDec | SymStr of StrDec | SymIncl of SigIncl
                       | SymConInst of SymInst | SymStrInst of SymInst | SymInclInst of SymInst
                       | SymConCase of SymCase | SymStrCase of SymCase | SymInclCase of SymCase

  fun modDecBase (SigDec(b,_)) = b
    | modDecBase (ViewDec(b,_,_,_,_)) = b
    | modDecBase (RelDec(b,_,_,_,_)) = b
  fun modDecName (SigDec(_,n)) = n
    | modDecName (ViewDec(_,n,_,_,_)) = n
    | modDecName (RelDec(_,n,_,_,_)) = n
  fun strDecName (StrDec(n, _, _, _, _, _)) = n
    | strDecName (StrDef(n, _, _, _, _)) = n
  fun strDecFoldName s =  IDs.mkString(strDecName s,"",".","")
  fun strDecQid (StrDec(_, q, _, _, _, _)) = q
    | strDecQid (StrDef(_, q, _, _, _)) = q
  fun strDecDom (StrDec(_, _, m, _, _, _)) = m
    | strDecDom (StrDef(_, _, m, _, _)) = m
  fun strDecImpl (StrDec(_, _, _, _, _, i)) = i
    | strDecImpl (StrDef(_, _, _, _, i)) = i

  fun symInstCid(ConInst(c, _, _)) = c
    | symInstCid(StrInst(c, _, _)) = c
    | symInstCid(InclInst(c, _, _)) = c
  fun symInstOrg(ConInst(_, O, _)) = O
    | symInstOrg(StrInst(_, O, _)) = O
    | symInstOrg(InclInst(_, O, _)) = O
  fun symRelCid(ConCase(c, _, _)) = c
    | symRelCid(StrCase(c, _, _)) = c
    | symRelCid(InclCase(c, _, _)) = c
  fun symRelOrg(ConCase(_, O, _)) = O
    | symRelOrg(StrCase(_, O, _)) = O
    | symRelOrg(InclCase(_, O, _)) = O

  (********************** Stateful data structures **********************)

  (* Invariants:
   module level declarations
   - modLookup m is defined for all 0 <= m < ! nextMid (0 is the toplevel, which is defined during initialization)
   - if modLookup m = SigDec _, then symLookup(m,l) is defined for all 0 <= l < modSize(m)
   - if modLookup m = ViewDec(_,d,_), then symLookup(m,l) yields the instantiation for (d,l)
   - if modLookup m = RelDec(_,d,_), then symLookup(m,l) yields the case for (d,l)
   
   symbol level declarations
   - if modLookup m = SigDec _, then symLookup(m,l) = SymCon _ or = SymStr _ or SymIncl _
   - if modLookup m = ViewDec(_,_,dom,cod,_), then
     * modLookup dom = SigDec _ and modLookup cod = SigDec _
     * symLookup (m,l) is defined for at most 0 <= l < modSize dom, and
       + if symLookup(m,l) = SymConInst _,  then symLookup(dom,l) = SymCon _
       + if symLookup(m,l) = SymStrInst _,  then symLookup(dom,l) = SymStr _
       + if symLookup(m,l) = SymInclInst _, then symLookup(dom,l) = SymIncl _
     * symLookup(m,l) does not have to be defined for all l even when m is total, e.g., if there are redundant includes
   - if modLookup m = RelDec(_,_,dom,cod,mors), then
     * modLookup dom = SigDec _ and modLookup cod = SigDec _
     * all morphisms in mors are valid from dom to cod
     * symLookup(m,l) is defined for at most 0 <= l < modSize dom, and
       + if symLookup(m,l) = SymConInst _,  then symLookup(dom,l) = SymCon _
       + if symLookup(m,l) = SymStrInst _,  then symLookup(dom,l) = SymStr _
       + if symLookup(m,l) = SymInclInst _, then symLookup(dom,l) = SymIncl _
     * symLookup(m,l) does not have to be defined for all l even when m is total, e.g., if there are redundant includes
   - if symLookup c = SymCon d, then d is valid and in normal form
   - if symLookup c = SymCon (ConDef _), then the definition is strict in all its arguments
   - I.Const(c) is valid iff symLookup c = SymCon (ConDec _)
   - I.Def(c) is valid   iff symLookup c = SymCon (ConDef _)
   - I.NSDef(c) is valid iff symLookup c = SymCon (AbrevDef _)
   
   elaborated symbol declarations
   Every declaration for s_1. ... .s_n.c generated by elaborating a structure can be seen as the result of applying
   - s_1. ... .s_n to c,
   - s_1. ... .s_{n-1} to s_n.c,
   - ..., or
   - s_1 to s_2. ... .s_n.c.
   If declTable contains (cid, condec) and cid represents the constant s_1. ... .s_n.c, then
   - (conDecQid condec) is [(CID(s_1. ... .s_n), CID(c)), ... ,(CID(s_1), CID(s_2. ... .s_n.c))],
   - (conDecName condec) is [s_1, ..., s_n, c].
   n = 0 iff a declaration is not generated elaborating a structure.
   For elaborated structures, the corresponding invariant holds.

   The mapping of cids to Qids and its inverse are redundant but maintained for faster lookup.
  *)

  (* modTable maps a mid m to a tuple of the module's cid and its size
     (size is -1 if the module is still open) *)
  (* @FR: get rid of having to keep track of size *)
  val modTable : (IDs.cid * IDs.lid) MH.Table = MH.new(499)

  (* declTable maps cids to symbol level declarations *)
  val declTable : Declaration CH.Table = CH.new(19999)

  (* inclTable is an index giving all module level objects included into a module *)
  datatype SigRelType = Self | Included of IDs.cid option | Ancestor of IDs.mid | AncIncluded
  datatype ModLevObject = ObjSig of IDs.mid * SigRelType | ObjMor of Morph | ObjRel of Rel
  val inclTable : ModLevObject list MH.Table = MH.new(299)
  
  (* structMapTable maps pairs ('s, 'c) to 's.c (where 'x is the cid of the name of x) - maintained for efficiency *)
  val structMapTable : IDs.cid CCH.Table = CCH.new(1999)
    
  (* scope holds the list of the currently open modules and their next available lid (innermost to outermost) *)
  type scopelist = (IDs.mid * IDs.lid) list 
  val scope : scopelist ref = ref nil
  (* savedScopes is a stack of scopes used in pushScope, popScope to temporarily switch back to the toplevel *)
  val savedScopes : (scopelist * (Declaration option)) list ref = ref nil
  (* the next available module id *)
  val nextMid : IDs.mid ref = ref 0
  
  (* implicit coercions: (T,m) in implicitOut(S) iff (S,m) in implicitIn(T) iff T can be coerced to S via m:S->T
     chained coercions are precomputed *)
  val implicitOut : (IDs.mid * Morph) list MH.Table = MH.new(50)
  val implicitIn  : (IDs.mid * Morph) list MH.Table = MH.new(50)

  (********************** Effect-free (lookup) methods **********************)
  fun getScope() = ! scope

  fun midToCid m = case MH.lookup modTable m
      of NONE => raise UndefinedMid m
       | SOME (c,_) => c
  fun modSize(m) =
     case List.find (fn (x,_) => x = m) (getScope())
       of SOME (_,l) => l                             (* size of open module stored in scope *)
        | NONE => #2 (valOf (MH.lookup modTable m))   (* size of closed module stored in modTable *)
                  handle Option => raise UndefinedMid(m)
  fun cidToMid c = case CH.lookup declTable c
      of SOME (SymMod(m,_)) => m
       | _ => raise UndefinedCid c
     
  fun modInclLookup(m) = valOf (MH.lookup inclTable m)
                                handle Option => raise UndefinedMid(m)
  fun sigIncluded(dom, cod) = List.exists
      (fn ObjSig(d, Self) => d = dom | ObjSig(d, Included _) => d = dom | ObjSig(d, AncIncluded) => d = dom | _ => false)
      (modInclLookup cod)
  fun sigRel(dom,cod) =
    case List.filter (fn ObjSig(d, _) => dom = d | _ => false) (modInclLookup cod)
      of nil => NONE
       | ObjSig(_,rel) :: tl => if List.exists (fn ObjSig(_, r) => r = AncIncluded | _ => false) tl
                                then SOME AncIncluded
                                else SOME rel
  fun symVisible(c, m) = case sigRel(IDs.midOf c, m)
    of SOME (Ancestor p) => if IDs.lidOf c < IDs.lidOf (midToCid p) then SOME (Ancestor p) else NONE
     | r => r

  fun symLookup(c : IDs.cid) = valOf (CH.lookup(declTable)(c))
                               handle Option => raise (UndefinedCid c)

  fun modLookup(m) =
    if m = 0 then SigDec("toplevel", nil)
             else case symLookup (midToCid m)
                    of SymMod (_,moddec) => moddec
                     | _ => raise UndefinedMid m

  fun sgnLookup (c : IDs.cid) = case symLookup c
    of SymCon d => d
     | _ => raise (UndefinedCid c)

  fun structLookup(c : IDs.cid) = case symLookup c
    of SymStr d => d
  | _ => raise (UndefinedCid c)

  fun structMapLookup (S,s') = CCH.lookup structMapTable (S,s')

  fun symQid(c : IDs.cid) = case symLookup c
       of SymCon condec => I.conDecQid condec
        | SymStr strdec => strDecQid strdec
        | SymIncl _ => nil
        (* should only be called for instantiations *)

  fun implicitLookupOut(d) = case MH.lookup implicitOut d of SOME l => l | NONE => nil
  fun implicitLookupIn(c)  = case MH.lookup implicitIn  c of SOME l => l | NONE => nil
  fun implicitLookup(d,c)  =
     let val outs = implicitLookupOut(d)
     in case List.find (fn (m, _) => m = c) outs
        of SOME(_, mor) => SOME mor
        | NONE => NONE
     end

  fun currentMod() = #1 (hd (getScope()))
  fun currentTargetSig() =
     let val m = currentMod()
     in case modLookup m
       of SigDec _ => m
        | ViewDec(_,_,_,cod,_) => cod
        | RelDec(_,_,_,cod,_) => cod
     end
  fun onToplevel() = currentMod() = 0
  (* true: currentMod() is SigDec, false: currentMod() is ViewDec *)
  fun inSignature() = case modLookup (currentMod())
                        of SigDec _ => true
                         | ViewDec _ => false
                         | RelDec _ => false
  fun inView() = case modLookup (currentMod())
                        of SigDec _ => false
                         | ViewDec _ => true
                         | RelDec _ => false
  fun inRelation() = case modLookup (currentMod())
                        of SigDec _ => false
                         | ViewDec _ => false
                         | RelDec _ => true

  (********************** Convenience methods **********************)
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
  fun symName(c) =
     case symLookup(c)
       of SymCon condec => IntSyn.conDecName condec
        | SymStr strdec => strDecName strdec
        (* should not be called for inclusions *)
  fun modName m = modDecName (modLookup m)

  fun symFoldName(c) = IDs.foldQName(symName c)
  fun modFoldName m = IDs.foldQName(modName m)
  fun fullFoldName(c) = IDs.foldFQName(modName (IDs.midOf c), symName c)
 
  fun modApp(f : IDs.mid -> unit) =
    let
      val length = ! nextMid
      fun doRest(m) = 
	if m = length then () else ((f m); doRest(m+1))
    in
      doRest(0)
    end
  
  (* changes state if f does *)
  fun sgnApp(m : IDs.mid, f : IDs.cid -> unit) =
    let
      val length = case modLookup m
        of SigDec _ => modSize m
         | ViewDec(_,_,dom,_,_) => modSize dom
         | RelDec(_,_,dom,_,_) => modSize dom
      fun doRest(l) =
	if l = length then () else (f(m,l); doRest(l+1))
    in
      doRest(0)
    end
  fun sgnAppC (f) = sgnApp(currentMod(), f)
  
  (********************** Effectful methods **********************)
  fun implicitAddOne(dom, cod, mor) =
  let
     val _ = if (sigIncluded(dom, cod)) then
     	raise Error("coercion from included signature not allowed") else ()
     val outs = implicitLookupOut dom
     val ins = implicitLookupIn cod
     val _ = if (List.exists (fn (c,_) => c = cod) outs) then
     	raise Error("multiple coercions from " ^ modFoldName dom ^ " to " ^ modFoldName cod) else ()
     (* no check needed due to invariant *)
   in (  
     MH.insert implicitOut (dom, (cod, mor) :: outs);
     MH.insert implicitIn  (cod, (dom, mor) :: ins)
   ) end

  fun implicitAdd(dom, cod, mor) =
  let
     val ins  = implicitLookupIn dom
     val outs = implicitLookupOut cod
  in (
     (* add mor *)
     implicitAddOne(dom, cod, mor);
     (* prepend mor to coercions out of cod *)
     List.map (fn (d, m) => implicitAddOne(d, cod, MorComp(m, mor))) ins;
     (* append mor to coercions into dom *)
     List.map (fn (c, m) => implicitAddOne(dom, c, MorComp(mor, m))) outs;
     (* connect coercions into dom and out of cod via mor *)
     List.map (fn (d, m) =>
       List.map (fn (c, n) => implicitAddOne(d, c, MorComp(m, MorComp(mor, n)))) outs
     ) ins;
     ()
  ) end

  fun pushScope() = let 
     val (_,nextLid) :: saveMods = List.rev (getScope())
     val saveModDecl = case saveMods
       of nil => NONE
        | (m,_) :: _ => (
          scope := [(0,nextLid-1)];
          MH.delete modTable m;
          CH.lookup declTable (0,nextLid-1)
        )
     val _ = savedScopes := (saveMods, saveModDecl) :: (! savedScopes)
  in () end

  fun popScope() = let
     val nextLid = case getScope() of (_,l) :: nil => l | _ => raise Error("not on toplevel")
     val (savedMods, savedModDecl) :: tl = ! savedScopes
     val _ = savedScopes := tl
     val mid = #1 (List.hd savedMods)
     val newCid = (0,nextLid)
     val _ = case savedModDecl
       of NONE => ()
        | SOME dec => (
            scope := List.rev ((0,nextLid + 1) :: savedMods);
            MH.insert modTable (mid, (newCid, ~1));
            CH.insert declTable (newCid, dec)
          )
  in newCid end

  fun declAddC(dec : Declaration) : IDs.cid = let
      val (c as (m,l)) :: scopetail = ! scope
      val _ = CH.insert(declTable)(c, dec)
      val _ = scope := (m, l+1) :: scopetail
  in c
  end

  fun modOpen(dec) =
     let
     	val _ = if inSignature() then () else raise Error("modules may only occur inside signatures")
        val m = ! nextMid
        val _ = nextMid := ! nextMid + 1
        val c = declAddC (SymMod (m,dec))
        val _ = MH.insert modTable (m, (c,~1))
        val (p,l) = List.hd (! scope)
        val pincls = modInclLookup p
        fun rewrite(Self) = Ancestor m
          | rewrite(Ancestor a) = Ancestor a
          | rewrite(Included _) = AncIncluded
          | rewrite(AncIncluded) = AncIncluded
        val incls = List.map (fn ObjSig(d,r) => ObjSig(d, rewrite r)) pincls (* no other cases possible in a signature *)
        val _ = case dec
          of SigDec _ => MH.insert inclTable (m, ObjSig(m, Self) :: incls)
          | ViewDec _ => MH.insert inclTable (m, incls)
          | RelDec _ => MH.insert inclTable (m, incls)
        val _ = scope := (m,0) :: (! scope)
     in
     	c
     end

  fun modClose() =
     let
     	val _ = if onToplevel() then raise Error("no open module to close") else ()
        val (m,l) :: tl = getScope()
        val _ = scope := tl
        val _ = MH.insert modTable (m, (midToCid m, l))
        val _ = case modLookup m
                  of ViewDec(_,_,dom,cod,true) => implicitAdd(dom, cod, MorView m)
                   | _ => ()
      in
         ()
      end

  fun sgnAddC (conDec : I.ConDec) =
    let
      val _ = if inSignature() then () else raise Error("constant declarations only allowed in signature")
      val c = declAddC (SymCon conDec)
      val q = I.conDecQid conDec
    in
      (* q = [(s_1,c_1),...,(s_n,c_n)] where every s_i maps c_i to c *)
      List.map (fn sc => CCH.insert structMapTable (sc, c)) q;
      c
    end
      
  fun structAddC(strDec : StrDec) =
    let
      val _ = if inSignature() then () else raise Error("structure declarations only allowed in signature")
      val c = declAddC(SymStr strDec)
      (* q = [(s_1,c_1),...,(s_n,c_n)] where every s_i maps c_i to c *)
      val q = strDecQid strDec
      val _ = List.map (fn sc => CCH.insert structMapTable (sc, c)) q
      val _ = if (strDecImpl strDec) then implicitAdd(strDecDom strDec, currentMod(), MorStr c) else ()
    in
      c
    end

  fun inclAddC(incl as SigIncl(dom,_)) =
     let
      val _ = if inSignature() then () else raise Error("inclusion only allowed in signature")
      val cod = currentMod()
      val c = declAddC (SymIncl incl)
      val codincls = modInclLookup cod
      val domincls = modInclLookup dom
      fun rewrite(ObjSig(m,Self)) = SOME (ObjSig(m,Included(SOME c)))
        | rewrite(ObjSig(m,Included _)) = SOME (ObjSig(m,Included NONE))
        | rewrite(ObjSig(m,Ancestor _)) = NONE (* ancestors of dom must already be ancestors of cod *)
        | rewrite(ObjSig(m,AncIncluded)) = NONE
        (* no other case possible in a signature *)
      val incls = List.mapPartial rewrite domincls
      val incls' = List.filter (fn x => List.all (fn y => not(x = y)) codincls) incls (* avoid duplicates *)
      val _ = MH.insert inclTable (cod, codincls @ incls')
      in
         c
      end
  
  fun instAddC(inst : SymInst) =
    let
      val _ = if inView() then () else raise Error("instantiations only allowed in view")
      val (m,l) :: scopetail = ! scope
      val c' = symInstCid inst
      val c = (m, IDs.lidOf c')
      (* make sure there are no clashes, i.e., symLookup must be undefined *)
      val _ = case CH.lookup declTable c
                of NONE => ()
                 | _ => raise Error("instantiation for this symbol or inclusion already defined")
    in
      (case inst
        of ConInst _ => CH.insert declTable (c, SymConInst inst)
         | StrInst _ => CH.insert declTable (c, SymStrInst inst)
         | InclInst(_,_,mor) => (
            CH.insert declTable (c, SymInclInst inst);
            MH.insert inclTable (m, (modInclLookup m) @ [ObjMor mor])
          )
      );
      scope := (m, l+1) :: scopetail;
      c 
    end

  fun caseAddC(rel : SymCase) =
    let
      val _ = if inRelation() then () else raise Error("declaration only allowed in logical relation")
      val (m,l) :: scopetail = ! scope
      val c' = symRelCid rel
      val c = (m, IDs.lidOf c')
      (* make sure there are no clashes, i.e., symLookup must be undefined *)
      val _ = case CH.lookup declTable c
                of NONE => ()
                 | _ => raise Error("case for this symbol or inclusion already defined")
    in
      (case rel
        of ConCase _ => CH.insert declTable (c, SymConCase rel)
         | StrCase _ => CH.insert declTable (c, SymStrCase rel)
         | InclCase(_,_,r) => (
            CH.insert declTable (c, SymInclCase rel);
            MH.insert inclTable (m, (modInclLookup m) @ [ObjRel r])
          )
      );
      scope := (m, l+1) :: scopetail;
      c 
    end

  fun reset () = (
    CH.clear declTable;               (* clear tables *)
    MH.clear modTable;
    MH.clear inclTable;
    CCH.clear structMapTable;
    MH.clear implicitOut;
    MH.clear implicitIn;
    savedScopes := nil;
    nextMid := 1;                       (* initial mid *)
    scope := [(0,0)];                   (* open toplevel signature *)
    MH.insert inclTable (0, [ObjSig(0,Self)])
    (* bogus entries for the toplevel signature, hopefully not needed anymore
    MH.insert modTable (0, (0,~1), ~1);
    MH.insert declTable((0,~1),(0, SymMod (0, SigDec("",nil))))
    *)
  )
 
  (********************** Convenience methods **********************)
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
    CH.insert(declTable)(c, conDec)
   *)
end (* functor ModSyn *)


(* ModSyn is instantiated with IntSyn right away. Both are visible globally. *)
structure ModSyn =
  ModSyn (structure IntSyn = IntSyn);

