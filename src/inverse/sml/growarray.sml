
structure GrowArray :> GROWARRAY =
struct

  type 'a growarray = (int * ('a option) Array.array) ref

  (* start with 16 cells, why not? *)
  fun empty () = ref (0, Array.array(16, NONE))

  fun growarray n i = ref (n, (Array.array(n, SOME i)))

  fun sub (ref (used, a)) n =
    if n < used andalso n >= 0
    then (case Array.sub(a, n) of
            NONE => raise Subscript
          | SOME z => z)
    else raise Subscript

  fun length (ref (l, _)) = l

  (* grow to accomodate at least n elements *)
  (* XXX this appears to be one element too conservative *)
  fun accomodate (r as ref(l, a)) n =
    if Array.length a >= (n + 1)
    then ()
    else
      let 
        fun nextpower x = 
          if x >= (n + 1) 
          then x
          else nextpower (x * 2)
        val ns = nextpower (Array.length a)
        val na = Array.tabulate(ns,
                                (fn i =>
                                 if i < l
                                 then Array.sub(a, i)
                                 else NONE))
      in
        r := (l, na)
      end

  fun update r n x =
    if n < 0 then raise Subscript
    else
      let 
        val _ = accomodate r n
        val (l, a) = !r
      in
        Array.update(a, n, SOME x);
        (* also update 'used' *)
        if n >= l
        then r := (n + 1, a)
        else ()
      end

  fun append (r as ref(n, _)) x =
    let
      val _ = accomodate r (n + 1)
      val (_, a) = !r
    in
      Array.update(a, n, SOME x);
      r := (n + 1, a)
    end

  fun finalize (ref (n, a)) =
    Array.tabulate (n, (fn x => case Array.sub(a, x) of
                                   NONE => raise Subscript
                                 | SOME z => z))

end