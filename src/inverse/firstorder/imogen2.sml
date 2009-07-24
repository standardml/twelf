
signature TWELF = 
   sig
      val message: string
      val doit: IntSyn.Exp * IntSyn.Exp * IntSyn.Uni -> IntSyn.Exp
   end

structure Twelf :> TWELF =
   struct 
      open GeneralExt 
      val message = "Imogen 1.0"
      fun doit _ = raise Unimplemented 
   end

signature TWELF_IMOGEN =
   sig
      structure Twelf: TWELF
   end 

structure TwelfImogen :> TWELF_IMOGEN = 
   struct 
      structure Twelf = Twelf
   end
