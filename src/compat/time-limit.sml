(* Default implementation of timeLimit *)
(* Ignores time limit *)

structure TimeLimit :> TIME_LIMIT =
struct
  exception TimeOut
  val timeLimit = fn t => fn f => fn x => f(x)
end;
