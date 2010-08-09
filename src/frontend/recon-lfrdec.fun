(* Reconstruct LFR declarations *)
(* Author: William Lovas *)

(* unclear if this should take all the same functor arguments as ReconConDec.
   what is the purpose of the fully-functorized style?  -wjl 08-12-2009 *)
functor ReconLFRDec (structure ReconTerm' : RECON_TERM)
  : RECON_LFRDEC =
struct
    structure ExtSyn = ReconTerm'
    type name = string

    exception Error of string

    fun error (r, msg) = raise Error (Paths.wrap (r, msg))

    datatype lfrdec =
        condec of (name * Paths.region) * ExtSyn.term
      | sortdec of name * (name * Paths.region)
      | subdec of (name * Paths.region) * (name * Paths.region)

    fun toString (condec ((n, _), tm)) = n ^ " :: ..."
      | toString (sortdec (n1, (n2, _))) = n1 ^ " << " ^ n2
      | toString (subdec ((n1, _), (n2, _))) = n1 ^ " <: " ^ n2

    fun findConst name r =
        let val qid = Names.Qid (nil, name)
        in
          case Names.constLookup qid of
                SOME cid => cid
              | NONE => error (r, "Invalid identifier\n"
                                ^ "Identifier `" ^ Names.qidToString qid
                                ^ "' is not a constant, definition, or abbreviation")
        end

    fun lfrdecToConDec (condec ((name, r_name), tm), Paths.Loc (fileName, r)) =
          let
            val _ = Names.varReset IntSyn.Null
            val _ = ExtSyn.resetErrors fileName
            (* look up name's type declaration *)
            val cid = findConst name r
            (* look up the classifier tm should refine
               (if name is a sort, this is the kind of the refined type *)
            val U = IntSyn.constType cid
            val i = IntSyn.constImp cid
            val L = case IntSyn.constUni cid of
                        IntSyn.Type => IntSyn.Sort
                      (* XXX not impossible: user could write, e.g.:
                            a : type.  s << a.  s :: sort.
                            a :: s.
                         this should probably give some sort of "wrong level"
                         error message, since refinement declarations are not
                         permitted for types. *)
                      (* | IntSyn.Kind => IntSyn.Class *)

                      (* impossible? *)
                      (* | IntSyn.Sort => IntSyn.Sort *)
                      (* this comes from an s << a declaration,
                         whose universe is always Class. *)
                      | IntSyn.Class => IntSyn.Class
            (* check the refinement restriction, reconstruct implicit args *)
           (* DEBUG
            val () = print ("*** checking refinement restriction: "
                          ^ Print.expToString (IntSyn.Null, U) ^ "\n")
           *)
            val (V, oc) = ExtSyn.lfrRecon (tm, i, U)
            val cd = (* Names.nameConDec XXX *) IntSyn.LFRConDec (cid, i, V, L)
            val ocd = Paths.dec (i, oc) (* XXX correct? *)
            val () = if !Global.chatter >= 3
                     then Msg.message ((Timers.time Timers.printing Print.conDecToString) cd ^ "\n")
                     else ()
            val () = if !Global.doubleCheck then
                        if (Timers.time Timers.checking SortCheck.check)
                                (IntSyn.Null, V, IntSyn.Uni L)
                         then ()
                         else error (r, "SortCheck doubleCheck failed")
                     else
                        ()
          in
            (cd, SOME ocd)
          end
      | lfrdecToConDec (sortdec (sname, (aname, r_aname)), Paths.Loc (fileName, r)) =
          let
            val _ = Names.varReset IntSyn.Null
            val _ = ExtSyn.resetErrors fileName
            (* lookup name's type declaration *)
            val cid = findConst aname r_aname
            val i = IntSyn.constImp cid
            val V = IntSyn.constType cid
            val cd = (* Names.nameConDec XXX *) IntSyn.LFRSortDec (sname, cid, i, V)
            val () = if !Global.chatter >= 3
                     then Msg.message ((Timers.time Timers.printing Print.conDecToString) cd ^ "\n")
                     else ()
          in
            (* XXX occurrence tree? *)
            (cd, NONE)
          end
      | lfrdecToConDec (subdec ((name1, r1), (name2, r2)), Paths.Loc (fileName, r)) =
          let
            val _ = Names.varReset IntSyn.Null
            val _ = ExtSyn.resetErrors fileName
            (* lookup name1 and name2's declarations *)
            val cid1 = findConst name1 r1
            val cid2 = findConst name2 r2
        (*
           It has been decided that this check is unimportant.
           XXX double check that all the important LFR theorems
           still hold even when this check is omitted.

            (* now check that cid1 and cid2 refine the same type,
               and that their classes match up exactly (<: and :> ?) *)
            val refs1 = Refinements.refinements cid1
            val refs2 = Refinements.refinements cid2
        *)
            val acid1 = Refinements.refinedType cid1
            val acid2 = Refinements.refinedType cid2
            val () = if acid1 <> acid2
                     then error (r, "Sorts in declaration refine different types")
                     else ()
            (* XXX handled in Names.installConstName -- does that seem right? *)
            (* val () = Subsort.addSubsort cid1 cid2 *)
            val cd = (* Names.nameConDec XXX *) IntSyn.LFRSubDec (cid1, cid2)
            val () = if !Global.chatter >= 3
                     then Msg.message ((Timers.time Timers.printing Print.conDecToString) cd ^ "\n")
                     else ()
          in
            (* XXX occurrence tree? *)
            (cd, NONE)
          end

end
