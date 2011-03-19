structure Version = 
struct

val current_version = "1.7.1"

val current_version_revision = "1813"

fun maybe true x = x
  | maybe false x = ""
  
val official = BuildId.revision = current_version_revision
val external = BuildId.revision = "exported"

val version_string = 
   "Twelf " ^ current_version ^ maybe (not official) "+" ^ " ("
   ^ maybe (not external andalso not official) ("r" ^ BuildId.revision ^ ", ")
   ^ "built " ^ BuildId.date ^ " on " ^ BuildId.hostname ^ ")"

end
