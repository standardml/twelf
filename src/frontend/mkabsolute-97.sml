(* mkAbsolute according to '97 version of SML Basis Library *)
structure MkAbsolute :> MK_ABSOLUTE =
struct
  fun mkAbsolute {path=path, relativeTo=relativeTo} =
      OS.Path.mkAbsolute (path, relativeTo)
end;
