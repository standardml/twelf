(* Elaboration for module expressions *)
(* Author: Kevin Watkins *)

functor ReconModule
  (structure Global : GLOBAL
   (*! structure IntSyn : INTSYN !*)
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn !*)
   (*! structure Paths' : PATHS !*)
   structure ReconTerm' : RECON_TERM
   (*! sharing ReconTerm'.IntSyn = IntSyn !*)
   (*! sharing ReconTerm'.Paths = Paths' !*)
   structure ModSyn' : MODSYN
   (*! sharing ModSyn'.IntSyn = IntSyn !*)
     sharing ModSyn'.Names = Names
   structure IntTree : TABLE where type key = int)
  : RECON_MODULE =
struct

  structure ExtSyn = ReconTerm'
  (*! structure Paths = Paths' !*)
  structure ModSyn = ModSyn'

  exception Error of string

  fun error (r, msg) = raise Error (Paths.wrap (r, msg))

  type strexp = unit -> IntSyn.mid * Paths.region

  fun strexp (ids, id, r) () =
      let
        val qid = Names.Qid (ids, id)
      in
        case Names.structLookup qid
          of NONE => error (r, "Undeclared structure " ^
                            Names.qidToString (valOf (Names.structUndef qid)))
           | SOME mid => (mid, r)
      end

  fun strexpToStrexp (f:strexp) = #1 (f ())

  datatype Inst =
      External of ExtSyn.term
    | Internal of IntSyn.cid

  type eqn = IntSyn.cid * Inst * Paths.region

  type inst = Names.namespace * eqn list -> eqn list

  fun coninst ((ids, id, r1), tm, r2) (ns, eqns) =
      let
        val qid = Names.Qid (ids, id)
      in
        case Names.constLookupIn (ns, qid)
          of NONE => error (r1, "Undeclared identifier "
                            ^ Names.qidToString (valOf (Names.constUndefIn (ns, qid))))
           | SOME cid => (cid, External tm (* this is wrong because constants in the sig being instantiated might incorrectly appear in tm -kw *), r2)::eqns
      end

  fun addStructEqn (rEqns, r1, r2, ids, mid1, mid2) =
      let
        val ns1 = Names.getComponents mid1
        val ns2 = Names.getComponents mid2
        fun push eqn = rEqns := eqn::(!rEqns)

        fun doConst (name, cid1) =
            case Names.constLookupIn (ns2, Names.Qid (nil, name))
              of NONE => error (r1, "Instantiating structure lacks component " ^
                                Names.qidToString (Names.Qid (rev ids, name)))
               | SOME cid2 => push (cid1, Internal cid2, r2)

        fun doStruct (name, mid1) =
            case Names.structLookupIn (ns2, Names.Qid (nil, name))
              of NONE => error (r1, "Instantiating structure lacks component " ^
                                Names.qidToString (Names.Qid (rev ids, name)))
               | SOME mid2 => addStructEqn (rEqns, r1, r2, name::ids, mid1, mid2)
      in
        Names.appConsts doConst ns1;
        Names.appStructs doStruct ns1
      end

  fun strinst ((ids, id, r1), strexp, r3) (ns, eqns) =
      let
        val qid = Names.Qid (ids, id)
        val mid1 = (case Names.structLookupIn (ns, qid)
                      of NONE => error (r1, "Undeclared structure "
                                        ^ Names.qidToString (valOf (Names.structUndefIn (ns, qid))))
                       | SOME mid1 => mid1)

        val (mid2, r2) = strexp ()
        val rEqns = ref eqns
      in
        addStructEqn (rEqns, r2, r3, nil, mid1, mid2);
        !rEqns
      end

  type whereclause = Names.namespace -> eqn list
  type sigexp = ModSyn.module option -> ModSyn.module * whereclause list

  fun thesig (SOME module) = (module, nil)

  fun sigid (id, r) NONE =
      (case ModSyn.lookupSigDef id
         of NONE => error (r, "Undefined signature " ^ id)
          | SOME module => (module, nil))

  fun wheresig (sigexp, instList) moduleOpt =
      let
        val (module, wherecls) = sigexp moduleOpt
        fun wherecl ns = foldr (fn (inst, eqns) => inst (ns, eqns)) nil instList
      in
        (module, wherecls @ [wherecl])
      end

  fun sigexpToSigexp (sigexp, moduleOpt) = sigexp moduleOpt

  type sigdef = ModSyn.module option -> string option * ModSyn.module * whereclause list

  fun sigdef (idOpt, sigexp) moduleOpt =
      let
        val (module, wherecls) = sigexp moduleOpt
      in
        (idOpt, module, wherecls)
      end

  fun sigdefToSigdef (sigdef, moduleOpt) = sigdef moduleOpt

  datatype StructDec =
      StructDec of string option * ModSyn.module * whereclause list
    | StructDef of string option * IntSyn.mid

  type structdec = ModSyn.module option -> StructDec

  fun structdec (idOpt, sigexp) moduleOpt =
      let
        val (module, inst) = sigexp moduleOpt
      in
        StructDec (idOpt, module, inst)
      end

  fun structdef (idOpt, strexp) NONE =
      let
        val mid = strexpToStrexp strexp
      in
        StructDef (idOpt, mid)
      end

  fun structdecToStructDec (structdec, moduleOpt) = structdec moduleOpt

  type eqnTable = (Inst * Paths.region) list ref IntTree.Table

  fun applyEqns wherecl namespace =
      let
        val eqns = wherecl namespace

        val table : eqnTable = IntTree.new (0)
        fun add (cid, Inst, r) =
            (case IntTree.lookup table cid
               of NONE => IntTree.insert table (cid, ref [(Inst, r)])
                | SOME rl => rl := (Inst, r)::(!rl))
        val _ = List.app add eqns

        fun doInst ((Internal cid, r), condec) =
              (ModSyn.strictify (ExtSyn.internalInst (condec, ModSyn.abbrevify (cid, IntSyn.sgnLookup cid), r))
              handle ExtSyn.Error msg =>
                raise ExtSyn.Error (msg ^ "\nin instantiation generated for "
                                    ^ Names.qidToString (Names.constQid cid)))
          | doInst ((External tm, r), condec) =
              ModSyn.strictify (ExtSyn.externalInst (condec, tm, r))

        fun transformConDec (cid, condec) =
            (case IntTree.lookup table cid
               of NONE => condec
                | SOME (ref l) => List.foldr doInst condec l)
      in
        transformConDec
      end

  fun moduleWhere (module, wherecl) =
      let
        val (mark, markStruct) = IntSyn.sgnSize ()
        val module' = ModSyn.instantiateModule (module, applyEqns wherecl)
        val _ = Names.resetFrom (mark, markStruct)
        (* val _ = IntSyn.resetFrom (mark, markStruct) *)
      in
        module'
      end

end
