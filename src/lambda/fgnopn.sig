(* Extensible operation on foreign matter *)
(* Author: Aleksey Kliger *)

signature FGN_OPN = sig
  type csid = int
  type rep = exn
  type arg
  type result

  type func = rep -> arg -> result

  val install : csid * func -> unit

  val apply : csid * rep -> arg -> result
end

