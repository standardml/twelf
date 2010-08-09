signature REFINEMENTS =
  sig
    exception Error of string

    (* [addRefinement cid did] adds did as a
       refinement declaration for the constant cid *)
    val addRefinement : IntSyn.cid -> IntSyn.did -> unit

    (* [refinementDids cid] returns the list of refinement
       declarations for the constant cid *)
    val refinementDids : IntSyn.cid -> IntSyn.did list

    (* [refinements cid] returns the list of refinements of cid *)
    val refinements : IntSyn.cid -> IntSyn.Exp list

    (* [refinedType scid] returns acid such that scid << acid *)
    val refinedType : IntSyn.cid -> IntSyn.cid

    (* reset () = ()
       Effect: clear refinement tables *)
    val reset : unit -> unit
  end
