(* External Syntax and Type Reconstruction *)
(* Author: Frank Pfenning *)

(* signature EXTSYN
   provides the interface for type reconstruction as seen
   by the parser
*)

signature EXTSYN =
sig

  structure Paths : PATHS

  type name = string			(* variable or constant name *)
  type term				(* term *)
  type dec				(* variable declaration *)

  val lcid : string * Paths.region -> term (* lower case id *)
  val ucid : string * Paths.region -> term (* upper case id *)
  val quid : string * Paths.region -> term (* quoted id, currently not parsed *)

  val app : term * term -> term		(* tm tm *)
  val arrow : term * term -> term	(* tm -> tm *)
  val backarrow : term * term -> term	(* tm <- tm *)
  val hastype : term * term -> term	(* tm : tm *)
  val omitobj : Paths.region -> term	(* _ as object, region for "_" *)
  val omittyp : Paths.region -> term	(* _ as type, region for "_" *)
  val pi : dec * term * Paths.region -> term (* {d} tm, region for "{d}" *)
  val lam : dec * term * Paths.region -> term (* [d] tm, region for "[d]" *)
  val typ : Paths.region -> term	(* type, region for "type" *)

  val dec : name option * term -> dec	(* id : tm | _ : tm *)
  val dec0 : name option -> dec		(* id | _  (type omitted) *)

  type condec				(* constant declaration *)
  val condec : name * term -> condec	(* id : tm *)
  val condef : name option * term * term option -> condec
					(* id : tm = tm | _ : tm = tm *)

  type query				(* query *)
  val query : name option * term -> query (* ucid : tm | tm *)

end;  (* signature EXTSYN *)

(* signature VARS
   provides the function which translates free variables either
   universally (in declarations) or existentially (in queries)
*)

signature VARS =
sig
  structure IntSyn : INTSYN

  val var : string * int -> (IntSyn.Exp * (IntSyn.Spine -> IntSyn.Exp)) 
end;  (* signature VARS *)

(* signature TP_RECON
   provides the interface to type reconstruction seen by Twelf 

   There are two structures with this signature,
   on translating free variables universally, the other existentially.
*)

signature TP_RECON =
sig

  structure IntSyn : INTSYN
  include EXTSYN

  exception Error of string

  val decToDec : IntSyn.dctx * dec -> IntSyn.Dec (* reconstructs D such that G |- D dec *)
  val termToExp : IntSyn.dctx * term -> IntSyn.Exp (* reconstructs V such that G |- V : type *)

  val queryToQuery : query * Paths.location
                     -> IntSyn.Exp * IntSyn.name option * (IntSyn.Exp * IntSyn.name) list
                     (* (A, SOME("X"), [(Y1, "Y1"),...] *)
		     (* where A is query type, X the optional proof term variable name *)
		     (* Yi the EVars in the query and "Yi" their names *)

  val condecToConDec : condec * Paths.location -> IntSyn.ConDec option * Paths.occConDec option
                     (* optional ConDec is absent for anonymous definitions *)

end;  (* signature TP_RECON *)
