(* Theorems *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)

signature THMSYN =
sig
  structure ModeSyn : MODESYN
  structure Paths : PATHS

  exception Error of string

  type Param = string option

  datatype Order =
    Varg of string list
  | Lex of Order list
  | Simul of Order list

  (* -bp *)
  datatype Predicate = Less | Leq | Eq

  datatype RedOrder = 
      RedOrder of Predicate * Order * Order
  
  datatype Callpats =
    Callpats of (ModeSyn.IntSyn.cid * Param list) list 

  (* Termination declaration *)
  datatype TDecl = 
    TDecl of Order * Callpats

  (* -bp *)
  (* Reduction declaration *)
  datatype RDecl = 
    RDecl of (RedOrder * Callpats)

  (* Theorem declaration  *)
  datatype ThDecl =
    ThDecl of (ModeSyn.IntSyn.Dec ModeSyn.IntSyn.Ctx * ModeSyn.IntSyn.Dec ModeSyn.IntSyn.Ctx) list
              * ModeSyn.IntSyn.Dec ModeSyn.IntSyn.Ctx * ModeSyn.Mode ModeSyn.IntSyn.Ctx * int

  (* Proof declaration *)
  datatype PDecl = 
    PDecl of int * TDecl

  (* World declaration *)
  datatype WDecl = 
    WDecl of (ModeSyn.IntSyn.Dec ModeSyn.IntSyn.Ctx * 
	      ModeSyn.IntSyn.Dec ModeSyn.IntSyn.Ctx) list * Callpats


  val theoremDecToConDec : ((string * ThDecl) * Paths.region) -> 
                           (ModeSyn.IntSyn.Dec ModeSyn.IntSyn.Ctx * ModeSyn.IntSyn.Dec ModeSyn.IntSyn.Ctx) list * ModeSyn.IntSyn.ConDec
  val theoremDecToModeSpine : ((string * ThDecl) * Paths.region) -> ModeSyn.ModeSpine
end;  (* signature THMSYN *)
