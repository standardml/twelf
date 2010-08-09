signature SUBSORT =
  sig
    exception Error of string
    val clear : unit -> unit
    val addSort : IntSyn.cid -> unit
    val addSubsort : IntSyn.cid -> IntSyn.cid -> unit
    val subsort : IntSyn.cid -> IntSyn.cid -> bool
    val printSubsorts : unit -> unit
  end
