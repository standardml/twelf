signature TIME_LIMIT =
sig
  exception TimeOut
  val timeLimit : Time.time option -> ('a -> 'b) -> 'a -> 'b
end;
