(* Integers Modulo a Prime Number *)
(* Author: Roberto Virga *)

functor IntegersMod (val p : int) :> FIELD =
struct

  val name = "integer" ^ (Int.toString p)

  type number = int

  fun normalize (n) = n mod p

  val zero = 0
  val one  = 1

  exception Div

  fun op~ (n) = Int.-(p, n)

  fun op+ (m, n) = normalize (Int.+(m, n))

  fun op- (m, n) = normalize (Int.-(m, n))

  fun op* (m, n) = normalize (Int.*(m, n))

  fun inverse (0) = raise Div
    | inverse (n) =
        let
          (* alternative: compute n^(p-2) *)
          fun inverse' i =
                if (normalize (Int.*(n, i)) = 1) then i
                else inverse' (Int.+(i, 1))
        in
          inverse' 1
        end

  fun fromInt (n) = normalize (n)

  fun fromString (str) =
        let
          val check = (List.all Char.isDigit)
        in
          if check (String.explode str) then
            (case (Int.fromString (str))
               of SOME (n) =>
                    if (n < p) then SOME (n)
                    else NONE
                | NONE => NONE)
          else NONE
        end

  val toString = Int.toString

end;  (* functor IntegersMod *)
