signature MSG =
sig
    val message : string -> unit
    val setMessageFunc : (string -> unit) -> unit
end

structure Msg :> MSG =
struct
 val default = print 
 val messageFunc = ref (default)
 fun setMessageFunc f = (messageFunc := f)
 fun message s = ((!messageFunc) s)
end
