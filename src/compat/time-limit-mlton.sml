
structure TimeLimit :> TIME_LIMIT =
struct 

exception TimeOut

val timeLimit : Time.time option -> ('a -> 'b) -> 'a -> 'b =
 fn NONE => (fn f => fn x => f x)
  | SOME t => fn f => fn x => TimeLimit.timeLimit t f x

end
