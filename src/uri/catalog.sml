signature CATALOG = sig
  (* sets the URL of the catalog server, typically something like http://localhost:8080 *)
  val setCatalogURL : URI.uri -> unit
  (* takes a namespace URI and a module name and returns its URL as a filename and a region *)
  val resolve : URI.uri * string -> string * Paths.region
  (* raised by resolve if resolution fails *)
  exception Error of string
end

structure Catalog : CATALOG = struct
  val catalogURL : URI.uri option ref = ref NONE

  exception Error of string

  fun setCatalogURL url = catalogURL := SOME url
  fun resolve(uri, modname) =
    if #scheme uri = SOME "file"
    then (* lookup in local file *)
       (* TODO *)
    else (* lookup in catalog *) 
      case catalogURL
          of NONE => raise Error("URI " ^ URI.uriToString uri ^ " cannot be resolved because no catalog server is configured")
           | SOME cat => 
               (* TODO *)
end