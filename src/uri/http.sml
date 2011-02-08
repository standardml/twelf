signature HTTP = sig
  val get : URI.uri -> string
end

structure HTTP = struct
  exception Error of string
  fun get(uri : URI.uri) =
  let
     val authority = valOf (#authority uri)
     val ipOpt = NetHostDB.getByName (#host authority)
     val addr = case ipOpt
        of NONE => raise Error("lookup failed")
         | SOME ip => INetSock.toAddr(NetHostDB.addr ip, getOpt(#port authority, 80))
     val sock = INetSock.TCP.socket()
     val _ = Socket.connect(sock, addr)
     (* val _ = Socket.bind(sock, INetSock.any 1000) *)
     val slice = Word8VectorSlice.full (Byte.stringToBytes "(* string data *)") 
     val sent = Socket.sendVec(sock, slice)
     val recslice = Socket.recvVec(sock, Word8Vector.maxLen)
     val response = Byte.bytesToString recslice
  in
     response
  end
end