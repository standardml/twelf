signature SORTS =
  sig
    exception Error of string

    datatype sort =
        Top
      | Inter of IntSyn.Exp * IntSyn.Exp
      | Basic of IntSyn.Exp
      | Unknown (* XXX should have its refined type *)

    val view : IntSyn.Exp -> sort
  end
