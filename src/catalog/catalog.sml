signature CATALOG = sig
  (* sets the URL of the catalog server, typically something like http://localhost:8080 *)
  val setCatalogURL : URI.uri -> unit
  (* takes a namespace URI and a module name and returns its URL *)
  val resolve : URI.uri * string -> URI.uri
  (* raised by resolve if resolution fails *)
  exception Error of string
end

structure Catalog : CATALOG = struct
  val catalogURL : URI.uri option ref = ref NONE

  exception Error of string

  fun setQuery(uri: URI.uri, query) = {scheme = #scheme uri, authority = #authority uri, abs = #abs uri, path = #path uri, query = SOME query, fragment = NONE}
  fun dropQueryFragment(uri: URI.uri) = {scheme = #scheme uri, authority = #authority uri, abs = #abs uri, path = #path uri, query = NONE, fragment = NONE}
  fun encode s = s

  fun indexOfAux(nil, c, seen) = ~1
    | indexOfAux(hd :: tl, c, seen) = if (hd = c) then seen else indexOfAux(tl, c, seen + 1)
  (* returns the first index of c in l (starting at 0), -1 if none *) 
  fun indexOf(l: char list, c: char) = indexOfAux(l, c, 0)
  
  fun setCatalogURL url = catalogURL := SOME url
  fun resolve(uri, modname) =
(*  if #scheme uri = SOME "file"
    then (* lookup in local file *)
       ("",0,0,0,0)
    else (* lookup in catalog *) *) 
      case catalogURL
          of ref NONE => raise Error("URI " ^ URI.uriToString uri ^ " cannot be resolved because no catalog server is configured")
           | ref (SOME cat) =>
             let
               val modURI : URI.uri = setQuery(uri, modname)
               val requestURI : URI.uri = setQuery(cat, "uri=" ^ (encode (URI.uriToString modURI)))
               val response : string = HTTP.getFromHeader("X-Twelf-Location", requestURI) handle e => raise Error("Cannot connect to catalog server at " ^ URI.uriToString(cat))
               val errSize = String.size("Unknown URI: ")
               (* check whether the server answered with Unknown URI: ... *)
               val _ = if (String.size(response) >= errSize) andalso (String.substring(response, 0, errSize) = "Unknown URI: ")
                        then raise Error("Unknown URI: " ^ response)
                        else ()
               val url = URI.parseURI response
               val file = dropQueryFragment(url)
               (* FR: for now, we just return the file name, later improvements could also use the exact region *)
             in
               file
             end
end