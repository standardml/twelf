
structure Context :> CONTEXT =
struct 

  structure L = Lib

  type 'a ctx = 'a list
  exception Context of string
                      
  val empty = []

  fun lookup(l,n) = 
      SOME (L.ith n l) handle Fail _ => NONE

  fun push (ctx,p) = p::ctx

  fun list l = l

end
