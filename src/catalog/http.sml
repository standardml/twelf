signature HTTP = sig
  (* get the correct HTML data *)
  val get : URI.uri -> string
  
  (* get the text from the HTTP header with key = Mydata. Replace back the encoded characters: `r with \r, `n with \n, `o with ` *)
  val getFromHeader : URI.uri -> string
end

(* WARNING: this only sends the path part of the URI, and ignores the query and fragment. However, if the "path" actually contains the query and fragment, it uses them *)
(* WARNING: if the server gives an HTTP error (like 404 Page not found), it simply returns the empty string *)
(* WARNING: this doesn't support chunked HTTP. Everything must be in one TCP packet. This leads to many troubles. *)
structure HTTP = struct
  exception Error of string
  fun get(uri : URI.uri) =
  let
     val authority = case #authority uri
         of SOME a => a 
          | NONE => raise Error("URI has no authority part")
     val host = #host authority
     val port = getOpt(#port authority, 80)
     val path = URI.relPathToString (#path uri)
     val ipOpt = NetHostDB.getByName host 
     val addr = case ipOpt
        of NONE => raise Error("lookup failed")
         | SOME ip => INetSock.toAddr(NetHostDB.addr ip, port)
     val sock = INetSock.TCP.socket()
     val _ = Socket.connect(sock, addr) handle e => raise Error("Cannot connect to " ^ host)
     val sendData = "GET /" ^ path ^ " HTTP/1.0\r\nHost: " ^ host ^ ":" ^ Int.toString(port) ^ "\r\nAccept: application/xml,text/html,text/plain\r\nAccept-Charset: ISO-8859-1,utf-8,utf8\r\nConnection: keep-alive\r\nCache-Control: max-age=0\r\n\r\n"
     val slice = Word8VectorSlice.full (Byte.stringToBytes sendData)
     val sent = Socket.sendVec(sock, slice)
     val recslice = Socket.recvVec(sock, Word8Vector.maxLen)
     val response = (Byte.bytesToString recslice)
     val _ = Socket.close(sock)
  in
     response
  end
(* 
  fun getContent(chars: char list) : char list = 
            if (List.length(chars) >= 4) andalso (List.take(chars,4) = explode "\r\n\r\n")
            then List.drop(chars,4)
            else if (List.length(chars) >= 1) then getContent(tl chars) else nil
     val responseContent = implode (getContent(explode response))
*)

  fun getFromHeader(uri : URI.uri) =
  let
     val response = get(uri)
     val stream = TEXT_IO.openString response
     fun getHeader(h, s) =
       case TEXT_IO.inputLine stream
         of NONE => NONE
          | SOME s =>
              if String.isPrefix(h,s)
              then String.extract(s, String.size h, NONE)
              else getHeader(h,s)
     val myData = getHeader("MyData: ", stream)
(*     val keySize = String.size("Mydata: ")
     fun getContent(chars: char list) : char list = 
            if (List.length(chars) >= keySize) andalso (List.take(chars,keySize) = explode "Mydata: ")
            then let
                     fun untilNewLine(chars: char list) : char list = 
                        if (List.length(chars) >= 2) andalso (List.take(chars,2) = explode "\r\n")
                        then nil
                        else if (List.length(chars) >= 1) 
                              then (hd chars)::untilNewLine(tl chars)
                              else nil
                  in
                     untilNewLine(List.drop(chars,keySize))
                  end
            else if (List.length(chars) >= 1) then getContent(tl chars) else nil
     (* incrementally replace all occurrences of patt in lst with repl *)
     fun replaceAll(lst: char list, patt: char list, repl: char list) : char list = 
         if (List.length(lst) >= List.length(patt)) andalso (List.take(lst, List.length(patt)) = patt)
         then repl @ replaceAll(List.drop(lst, List.length(patt)), patt, repl)
         else if (List.length(lst) >= 1)
               then (hd lst)::replaceAll(tl lst, patt, repl)
               else nil
     val mydataContent = implode (replaceAll(replaceAll(replaceAll(getContent(explode response), explode "`r", explode "\r"), explode "`n", explode "\n"), explode "`o", explode "`"))
*)
  in
     myData
  end
end

(*
fun printStackTrace e =
 let val ss = SMLofNJ.exnHistory e
 in
 print ("uncaught exception " ^ (exnMessage e) ^ "\n");
 app (fn s => print ("\t" ^ s ^ "\n")) ss
end*)