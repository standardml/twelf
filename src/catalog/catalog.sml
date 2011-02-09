signature CATALOG = sig
  (* sets the URL of the catalog server, typically something like http://localhost:8080 *)
  val setCatalogURL : URI.uri -> unit
  (* takes a namespace URI and a module name and returns its URL as a filename and a region *)
  val resolve : URI.uri * string -> string * int * int * int * int
  (* raised by resolve if resolution fails *)
  exception Error of string
end

structure Catalog : CATALOG = struct
  val catalogURL : URI.uri option ref = ref NONE

  exception Error of string

  fun setQuery(uri, query) = {scheme = #scheme uri, authority = #authority uri, abs = #abs uri, path = #path uri, query = SOME query, fragment = NONE}
  fun encode s = s
  
  fun setCatalogURL url = catalogURL := SOME url
  fun resolve(uri, modname) =
    if #scheme uri = SOME "file"
    then (* lookup in local file *)
       ("",0,0,0,0)
    else (* lookup in catalog *) 
      case catalogURL
          of ref NONE => raise Error("URI " ^ URI.uriToString uri ^ " cannot be resolved because no catalog server is configured")
           | ref (SOME cat) =>
             let
               val modURI : URI.uri = setQuery(uri, modname)
               val requestURI : URI.uri = setQuery(cat, "uri=" ^ (encode (URI.uriToString modURI)))
               val modURL : string = HTTP.getFromHeader(requestURI) handle e => raise Error("Cannot connect to catalog server at " ^ URI.uriToString(cat))
               val errSize = String.size("Unknown URI: ")
               (* check whether the server answered with Unknown URI: ... *)
               val _ = if (String.size(modURL) >= errSize) andalso (String.substring(modURL, 0, errSize) = "Unknown URI: ")
                        then raise Error(modURL)
                        else true
               fun findPosition(s: char list, c: char) : int = 
                  let 
                     fun find(nil, _) = 0
                       | find(head::rest, c) = if (head = c) then 0 else 1 + find(rest, c)
                     val rawPos : int = find(s, c)
                  in if (rawPos = List.length(s)) then ~1 else rawPos
                  end
               val positionOfSharp : int = findPosition(explode modURL, #"#")
               val fileURL : string = String.substring(modURL, 0, positionOfSharp)
               val fragment : char list = List.drop(explode modURL, positionOfSharp + 3)   (* of the form 37,0),(48,1)) *)
               val posOfFirstComma : int = findPosition(fragment, #",")
               val firstLine : int = valOf (Int.fromString(implode (List.take(fragment, posOfFirstComma))))
               val f2 : char list = List.drop(fragment, posOfFirstComma + 1)   (* of the form 0),(48,1)) *)
               val posOfFirstClosingBracket : int = findPosition(f2, #")")
               val firstCol : int = valOf (Int.fromString(implode (List.take(f2, posOfFirstClosingBracket))))
               val f3 : char list = List.drop(f2, posOfFirstClosingBracket + 3)   (* of the form 48,1)) *)
               val posOfSecondComma : int = findPosition(f3, #",")
               val lastLine : int = valOf (Int.fromString(implode (List.take(f3, posOfSecondComma))))
               val f4 : char list = List.drop(f3, posOfSecondComma + 1)
               val lastCol : int = valOf (Int.fromString(implode f4))
             in
               (fileURL, firstLine, firstCol, lastLine, lastCol)
             end
end