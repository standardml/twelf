(* Trailing Abstract Operations *)
(* Author: Roberto Virga *)

structure Trail : TRAIL =
struct

  local
    datatype 'a  Trail =
      Cons of 'a * 'a Trail
    | Mark of 'a Trail
    | Nil

    type 'a trail = 'a Trail ref

    fun trail () = ref Nil

    fun reset trail =
          trail := Nil

    fun mark trail =
          trail := Mark (!trail)

    fun unwind (trail, undo) =
          let
            fun unwind' Nil = Nil
              | unwind' (Mark trail) = trail
              | unwind' (Cons (action, trail)) =
                  (undo action ; unwind' trail)
          in
            trail := unwind' (!trail)
          end

    fun log (trail, action) =
          trail := Cons (action, !trail)

  in
    type 'a trail = 'a trail

    val trail = trail

    val reset = reset
    val mark = mark
    val unwind = unwind
    val log = log
  end (* local ... *)
end; (* structure Trail *)
