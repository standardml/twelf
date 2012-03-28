(* Initialization *)
(* Author: Carsten Schuermann *)

functor MTPInit (structure MTPGlobal : MTPGLOBAL
                 structure MTPData : MTPDATA
                 (*! structure IntSyn : INTSYN !*)
                 structure Names : NAMES
                 (*! sharing Names.IntSyn = IntSyn !*)
                 (*! structure FunSyn' : FUNSYN !*)
                 (*! sharing FunSyn'.IntSyn = IntSyn !*)
                 structure StateSyn' : STATESYN
                 (*! sharing StateSyn'.FunSyn = FunSyn' !*)
                 structure Formatter : FORMATTER
                 structure Whnf : WHNF
                 (*! sharing Whnf.IntSyn = IntSyn !*)
                 structure Print : PRINT
                   sharing Print.Formatter = Formatter
                   (*! sharing Print.IntSyn = IntSyn !*)
                 structure FunPrint : FUNPRINT
                 (*! sharing FunPrint.FunSyn = FunSyn' !*)
                   sharing FunPrint.Formatter = Formatter)
  : MTPINIT =
struct
  (*! structure FunSyn = FunSyn' !*)
  structure StateSyn = StateSyn'

  exception Error of string

  local
    structure I = IntSyn
    structure F = FunSyn
    structure S = StateSyn
    structure Fmt = Formatter

    (* init (F, OF) = Ss'

       Invariant:
       If   . |- F formula    and   F in nf
       and  . |- OF order
       then Ss' is a list of initial states for the theorem prover
    *)

    fun init (F, OF) =
      let
        fun init' ((G, B), S.All (_, O), F.All (F.Prim D, F'), Ss) =
            let
              val D' = Names.decName (G, D)
            in
              init' ((I.Decl (G, D'),
                     I.Decl (B, S.Lemma (S.Splits (!MTPGlobal.maxSplit)))),
                     O, F', Ss)
            end
              (* it is possible to calculuate
                 index/induction variable information here
                 define occursOrder in StateSyn.fun  --cs *)
   (*      | init' (G, B, O, (F.All (F.Block _, F), s)) =
           no such case yet  --cs *)
          | init' (GB, S.And (O1, O2), F.And (F1, F2), Ss) =
              init' (GB, O1, F1, init' (GB, O2, F2, Ss))
          | init' (GB, O, F' as F.Ex _, Ss) =
              S.State (List.length Ss + 1, GB, (F, OF), 1, O, nil, F') :: Ss
          | init' (GB, O, F' as F.True, Ss) =
              S.State (List.length Ss + 1, GB, (F, OF), 1, O, nil, F') :: Ss
            (* added in case there are no existentials -fp *)
      in
        (Names.varReset I.Null;
         MTPData.maxFill := 0;
         init' ((I.Null, I.Null), OF, F, nil))
      end

  in
    val init = init
  end (* local *)
end; (* functor Init *)
