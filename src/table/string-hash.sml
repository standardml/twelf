(* String Hash Table *)
(* Author: Frank Pfenning *)

structure StringHash :> STRING_HASH =
struct
  fun stringHash (s) =
      (* sample 4 characters from string *)
      let
	fun num (i) = Char.ord (String.sub (s,i)) mod 128
	val n = String.size (s)
      in
	if n = 0 then 0
	else let
	       val a = n-1
	       val b = n div 2
	       val c = b div 2
	       val d = b + c
	     in
	       num(a)+64*(num(b)+64*(num(c)+64*num(d)))
	     end
      end
  (* recurse over list, adding hash values for single strings as computed above *)
  fun stringListHash(nil) = 0
    | stringListHash(s :: rest) = (stringHash(s) + 5 * stringListHash(rest)) mod 16777216  (* modulo needed to prevent Overflow exception *)
end;  (* structure StringHash *)
