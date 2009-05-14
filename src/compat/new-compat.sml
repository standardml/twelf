
structure Compat =
struct

fun inputLine instream = getOpt (TextIO.inputLine instream, "")

end
