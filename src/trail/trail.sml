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


    fun suspend (trail, copy) =
      let
	fun suspend' Nil = Nil
(*	  | suspend' (Mark trail) = (Mark (suspend' trail))*)
	  | suspend' (Mark trail) = (suspend' trail)
	  | suspend' (Cons (action, trail)) =
	  Cons (copy action,  suspend' trail)
	val ftrail = suspend' (!trail)
      in
	ref ftrail
      end

    fun resume (ftrail, trail, reset) = 
      let
	fun resume' Nil = Nil
(*	  | resume' (Mark ftrail) = (Mark (resume' ftrail)) *)
	  | resume' (Mark ftrail) = resume' ftrail
	  | resume' (Cons (faction, ftrail)) = 
	  Cons (reset faction, resume' ftrail)
	val trail' = resume' (!ftrail)
      in 
       trail := trail'
      end 


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

    val suspend = suspend
    val resume = resume

    val reset = reset
    val mark = mark
    val unwind = unwind
    val log = log
  end (* local ... *)
end; (* structure Trail *)
