(* Trailing Abstract Operations *)
(* Author: Roberto Virga *)

signature TRAIL =
sig

  type 'a trail

  val trail : unit -> 'a trail

  val reset  : 'a trail -> unit
  val mark   : 'a trail -> unit
  val unwind : 'a trail * ('a -> unit) -> unit
  val log    : 'a trail * 'a -> unit
end; (* signature TRAIL *)
