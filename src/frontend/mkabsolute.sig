signature MK_ABSOLUTE =
sig
  val mkAbsolute : {path:string, relativeTo:string} -> string
end;
