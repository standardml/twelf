(* Compatibility shim from Basis-current Socket to Basis-97 Socket *)
(* Author: Christopher Richards *)

structure CompatSocketIO :> COMPAT_SOCKET_IO =
struct
fun sendVec (sock, vs) = Socket.sendVec (sock, Word8VectorSlice.full vs)
end
