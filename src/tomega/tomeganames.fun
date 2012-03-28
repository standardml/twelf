(* Naming *)
(* Author: Carsten Schuermann *)

structure TomegaNames : TOMEGANAMES=
  struct
    structure T = Tomega
    structure I = IntSyn

    fun decName (Psi, T.UDec D) = T.UDec (Names.decName (T.coerceCtx Psi, D))
      | decName (Psi, T.PDec (x, F, TC1, TC2)) =
        let
          val I.NDec x' =  Names.decName (T.coerceCtx Psi, I.NDec x)
        in
          T.PDec (x', F, TC1, TC2)
        end
  end