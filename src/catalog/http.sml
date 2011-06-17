(* HTTP client *)
(* Alin Iacob, Florian Rabe *)

signature HTTP = sig
  (* send a GET request and return whole result as string *)
  (* If the server returns an HTTP error (like 404 Page not found), it simply returns the empty string *)
  val get : URI.uri -> string
  (* send GET request and return the value of a specific header of the response. *)
  val getFromHeader : URI.uri * string -> string
end

(* This doesn't seem to support chunked HTTP - everything must be in one TCP packet. This leads to many troubles. *)
structure HTTP = struct
  exception Error of string
  fun get(uri : URI.uri) =
  let
     val authority = case #authority uri
         of SOME a => a 
          | NONE => raise Error("URI has no authority part")
     val host = #host authority
     val port = getOpt(#port authority, 80)
     val requri = URI.relPathToString (#path uri) ^ (case #query uri of SOME q => "?" ^ q | _ => "") 
     val ipOpt = NetHostDB.getByName host 
     val addr = case ipOpt
        of NONE => raise Error("lookup failed")
         | SOME ip => INetSock.toAddr(NetHostDB.addr ip, port)
     val sock = INetSock.TCP.socket()
     val _ = Socket.connect(sock, addr) handle e => raise Error("Cannot connect to " ^ host)
     val sendData = "GET /" ^ requri ^ " HTTP/1.0\r\nHost: " ^ host ^ ":" ^ Int.toString(port) ^ "\r\nAccept: application/xml,text/html,text/plain\r\nAccept-Charset: ISO-8859-1,utf-8,utf8\r\nConnection: keep-alive\r\nCache-Control: max-age=0\r\n\r\n"
     val slice = Word8VectorSlice.full (Byte.stringToBytes sendData)
     val sent = Socket.sendVec(sock, slice)
     val recslice = Socket.recvVec(sock, Word8Vector.maxLen)
     val response = (Byte.bytesToString recslice)
     val _ = Socket.close(sock)
  in
     response
  end

  fun getFromHeader(header: string, uri : URI.uri) =
  let
     val response = get(uri)
     val stream = TextIO.openString response
     fun getHeader(s) =
       case TextIO.inputLine s
         of NONE => ""
          | SOME line =>
              if String.isPrefix header line
              then String.extract(line, (String.size header) + 2, NONE)
              else getHeader(s)
     val myData = getHeader(stream)
  in
     myData
  end
end