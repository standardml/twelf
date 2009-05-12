
structure ImogenDec =
struct 



signature IMOGEN_DEC =
   sig
      structure ExtSyn: EXTSYN
      datatype dec = String of string
                   | Term of ExtSyn.term
      val handleDec: dec -> unit
   end

functor ImogenDecFn(ExtSyn: EXTSYN) : IMOGEN_DEC =
   struct
      structure ExtSyn = ExtSyn
      datatype dec = String of string
                   | Term of ExtSyn.term
(*                    | Job of ReconTerm.Job *)
      fun handleDec _ = raise Fail "Unimplemented"
   end


end
