(* Mode Syntax *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning, Roberto Virga *)

signature MODESYN =
sig

  (*! structure IntSyn : INTSYN !*)

  datatype Mode = Plus | Star | Minus | Minus1
  datatype ModeSpine = Mnil | Mapp of Marg * ModeSpine
  and Marg = Marg of Mode * string option

  val modeEqual : Mode * Mode -> bool
  val modeToString : Mode -> string
end;  (* signature MODESYN *)


structure ModeSyn :> MODESYN =
struct

  exception Error of string

  datatype Mode = Plus | Star | Minus | Minus1
  datatype ModeSpine = Mnil | Mapp of Marg * ModeSpine
  and  Marg = Marg of Mode * string option
   

  (* modeEqual (M1, M2) = true iff M1 = M2 *)
  fun modeEqual (Plus, Plus) = true
    | modeEqual (Star, Star) = true
    | modeEqual (Minus, Minus) = true
    | modeEqual (Minus1, Minus1) = true
    | modeEqual (_, _) = false

  (* modeToString M = string
    
       converts a mode into a string for error messages
  *)
  fun modeToString Plus = "input (+)"
    | modeToString Star = "unrestricted (*)"
    | modeToString Minus = "output (-)"
    | modeToString Minus1 = "unique output (-1)"

end;  (* structure ModeSyn *)
