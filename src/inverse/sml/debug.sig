
signature DEBUG =
sig

  exception Assert of exn

  (* general *) 
  val enable : unit -> unit
  val disable : unit -> unit

  (* assertions *) 
  val enable_assertions : unit -> unit
  val disable_assertions : unit -> unit
  val assert : bool * exn -> unit (* raises Assert *)

  (* printing *) 
  val enable_printing : unit -> unit
  val disable_printing : unit -> unit
  val print : string -> unit

end
