(* mkAbsolute according to newer versions of SML Standard Basis Library *)

structure MkAbsolute :> MK_ABSOLUTE =
struct
  val mkAbsolute = OS.Path.mkAbsolute
end;
