(* Abstract Machine for Tracing *)
(* Author: Frank Pfenning *)

signature TMACHINE =
sig

  include ABSMACHINE

  val trace : bool ref

end;  (* signature ABSMACHINE *)
