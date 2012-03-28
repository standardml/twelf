(* Rationals *)
(* Author: Roberto Virga *)

functor Rationals (Integers : INTEGERS) : RATIONALS =
struct

  structure Integers = Integers

  val name = "rational"

  exception Div = Div

  local
    structure I = Integers

    datatype number =                          (* Rational number:              *)
      Fract of Int.int * I.int * I.int         (* q := Fract (sign, num, denom) *)

    val zero = Fract (0, I.fromInt(0), I.fromInt(1))
    val one  = Fract (1, I.fromInt(1), I.fromInt(1))

    exception Div

    fun normalize (Fract (0, _, _)) = zero
      | normalize (Fract (s, n, d)) =
          let
            fun gcd (m, n) =
                  if (m = I.fromInt(0)) then n
                  else if (n = I.fromInt(0)) then m
                  else if I.>(m, n) then gcd (I.mod(m, n), n)
                  else gcd (m, I.mod(n, m))
            val g = gcd (n, d)
          in
            Fract (s, I.div(n, g), I.div(d, g))
          end

    fun op~ (Fract (s, n, d)) = (Fract (Int.~(s), n, d))

    fun op+ (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
          let
            val n = I.+(I.*(I.*(I.fromInt(s1), n1), d2),
                        I.*(I.*(I.fromInt(s2), n2), d1))
          in
            normalize (Fract (I.sign(n), I.abs(n), I.*(d1, d2)))
          end

    fun op- (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
          let
            val n = I.-(I.*(I.*(I.fromInt(s1), n1), d2),
                        I.*(I.*(I.fromInt(s2), n2), d1))
          in
            normalize (Fract (I.sign(n), I.abs(n), I.*(d1, d2)))
          end

    fun op* (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
          normalize (Fract(Int.*(s1, s2), I.*(n1, n2), I.*(d1, d2)))

    fun inverse (Fract (0, _, _)) = raise Div
      | inverse (Fract (s, n, d)) = (Fract (s, d, n))

    fun sign (Fract (s, n, d)) = s

    fun numerator (Fract (s, n, d)) = n

    fun denominator (Fract (s, n, d)) = d

    fun abs (Fract (s, n, d)) = (Fract (Int.abs(s), n, d))

    fun compare (Fract (s1, n1, d1), Fract( s2, n2, d2)) =
          I.compare (I.*(I.*(I.fromInt(s1), n1), d2),
                     I.*(I.*(I.fromInt(s2), n2), d1))

    fun op> (q1, q2) = (compare (q1, q2) = GREATER)

    fun op< (q1, q2) = (compare (q1, q2) = LESS)

    fun op>= (q1, q2) = (q1 = q2) orelse (q1 > q2)

    fun op<= (q1, q2) = (q1 = q2) orelse (q1 < q2)

    fun fromInt (n) =
          (Fract (Int.sign (n),
                  I.fromInt (Int.abs (n)),
                  I.fromInt (1)))

    fun fromString (str) =
          let
            fun check_numerator (chars as (c :: chars')) =
                  if (c = #"~")
                  then (List.all Char.isDigit chars')
                  else (List.all Char.isDigit chars)
              | check_numerator nil =
                  false
            fun check_denominator (chars) =
                  (List.all Char.isDigit chars)
            val fields = (String.fields (fn c => (c = #"/")) str)
        in
          if (List.length fields = 1)
          then
            let
              val numerator = List.nth (fields, 0)
            in
              if (check_numerator (String.explode (numerator)))
              then
                case (I.fromString (numerator))
                  of SOME (n) =>
                       SOME (Fract(I.sign(n),
                                   I.abs(n),
                                   I.fromInt(1)))
                   | _ =>
                       NONE
              else
                NONE
            end
          else if (List.length fields = 2)
          then
            let
              val numerator = List.nth (fields, 0)
              val denominator = List.nth (fields, 1)
            in
              if (check_numerator (String.explode (numerator)))
                andalso (check_denominator (String.explode (denominator)))
              then
                case (I.fromString (numerator), I.fromString (denominator))
                  of (SOME (n), SOME (d)) =>
                       SOME (normalize (Fract (I.sign(n), I.abs(n), d)))
                   | _ =>
                       NONE
              else
                NONE
            end
          else
            NONE
        end

    fun toString (Fract(s, n, d)) =
          let
            val nStr = I.toString (I.* (I.fromInt(s), n))
            val dStr = I.toString d
          in
            if (d = I.fromInt(1)) then nStr else (nStr ^ "/" ^ dStr)
          end

    fun fromInteger (n) =
          Fract (I.sign (n), I.abs (n), I.fromInt(1))

    fun floor (q as Fract (s, n, d)) =
          if Int.>=(s, 0)
          then I.quot (n, d)
          else Integers.~(ceiling (~ q))

    and ceiling (q as Fract (s, n, d)) =
          if Int.>=(s, 0)
          then I.quot (I.+ (n, I.- (d, I.fromInt(1))), d)
          else Integers.~(floor (~ q))

  in
    type number = number

    val zero = zero
    val one = one

    val op~ = op~
    val op+ = op+
    val op- = op-
    val op* = op*
    val inverse = inverse

    val fromInt = fromInt
    val fromString = fromString
    val toString = toString

    val sign = sign
    val abs = abs

    val op> = op>
    val op< = op<
    val op>= = op>=
    val op<= = op<=
    val compare = compare

    val fromInteger = fromInteger
    val floor = floor
    val ceiling = ceiling

    val numerator = numerator
    val denominator = denominator
  end
end;  (* structure Rationals *)
