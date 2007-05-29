
structure Debug :> DEBUG = 
struct 

  exception Assert of exn

  val assert' = ref true
  val print' = ref true

  fun enable() = (assert' := true;print' := true)
  fun disable() = (assert' := true;print' := true)

  fun enable_assertions() = assert' := true;
  fun disable_assertions() = assert' := false;

  fun enable_printing() = print' := true;
  fun disable_printing() = print' := false;

  fun assert (c,exn) =
      if !assert' then
        if c then () 
        else raise Assert exn
      else ()

  fun print s = if !print' then TextIO.print (s ^ "\n") else ()

end
