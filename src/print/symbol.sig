signature SYMBOL =
sig

  val str : string -> string * int
  val evar : string -> string * int
  val bvar : string -> string * int
  val const : string -> string * int
  val label : string -> string * int
  val skonst : string -> string * int
  val def : string -> string * int
  val fvar : string -> string * int

  val sym : string -> string * int

end;  (* signature SYMBOL *)
