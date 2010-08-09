structure Sorts =
  struct
    exception Error of string
    fun assert (b, s) = if b then () else raise Error s

    structure I = IntSyn
    fun lfrCid name = valOf (Names.constLookup (Names.Qid (nil, name)))

    datatype sort =
        Top
      | Inter of I.Exp * I.Exp
      | Basic of I.Exp
      | Unknown (* XXX should really have its refined type as an argument *)

    fun view (R as I.Root (I.Const cid, S)) =
        if cid = lfrCid "#" then
            case S of I.Nil => Top
                    | _ => raise Error "sort `#' applied to arguments (bug?)"
        else if cid = lfrCid "^" then
            case S of I.App (U1, I.App (U2, I.Nil)) => Inter (U1, U2)
                    | _ => raise Error "sort `^' applied to != 2 arguments (bug?)"
        else if cid = lfrCid "<<" then
            case S of I.App (U1, I.App (U2, I.Nil)) => view U1
                    | _ => raise Error "refinement operator `<<' applied to != 2 arguments (bug?)"
        else if cid = lfrCid "?" then
            case S of I.Nil => Unknown
                    | _ => raise Error "unknown sort `?' applied to arguments (bug?)"
        else
            Basic R
      | view U = Basic U

  end
