(* Theorems *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)

signature THMSYN =
sig
  structure Names : NAMES

  exception Error of string

  (*! type Param = string option !*)

  datatype Order =
    Varg of string list
  | Lex of Order list
  | Simul of Order list

  (* -bp *)
  datatype Predicate = Less | Leq | Eq

  datatype RedOrder = 
      RedOrder of Predicate * Order * Order
  
  datatype Callpats =
    Callpats of (IntSyn.cid * (string option) list) list 

  (* Termination declaration *)
  datatype TDecl = 
    TDecl of Order * Callpats

  (* -bp *)
  (* Reduction declaration *)
  datatype RDecl = 
    RDecl of (RedOrder * Callpats)

   (* Tabled declaration *)
   datatype TabledDecl = 
    TabledDecl of IntSyn.cid

   (* KeepTable declaration *)
   datatype KeepTableDecl = 
    KeepTableDecl of IntSyn.cid

  (* Theorem declaration  *)
  datatype ThDecl =
    ThDecl of (IntSyn.Dec IntSyn.Ctx * IntSyn.Dec IntSyn.Ctx) list
              * IntSyn.Dec IntSyn.Ctx * ModeSyn.Mode IntSyn.Ctx * int

  (* Proof declaration *)
  datatype PDecl = 
    PDecl of int * TDecl

  (* World declaration *)
(*  datatype WDecl = 
    WDecl of (IntSyn.Dec IntSyn.Ctx * 
	      IntSyn.Dec IntSyn.Ctx) list * Callpats
*)
  datatype WDecl = 
    WDecl of Names.Qid list * Callpats

  val theoremDecToConDec : ((string * ThDecl) * Paths.region) -> 
                           (IntSyn.Dec IntSyn.Ctx * IntSyn.Dec IntSyn.Ctx) list * IntSyn.ConDec
  val theoremDecToModeSpine : ((string * ThDecl) * Paths.region) -> ModeSyn.ModeSpine
end;  (* signature THMSYN *)
