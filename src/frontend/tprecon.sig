(* External Syntax and Type Reconstruction *)
(* Author: Frank Pfenning *)

(* signature EXTSYN
   provides the interface for type reconstruction as seen
   by the parser
*)

signature EXTSYN =
sig

  structure Paths : PATHS

  type term				(* term *)
  type dec				(* variable declaration *)

  val lcid : string list * string * Paths.region -> term (* lower case id *)
  val ucid : string list * string * Paths.region -> term (* upper case id *)
  val quid : string list * string * Paths.region -> term (* quoted id, currently not parsed *)
  val scon : string * Paths.region -> term (* string constant *)

  val app : term * term -> term		(* tm tm *)
  val arrow : term * term -> term	(* tm -> tm *)
  val backarrow : term * term -> term	(* tm <- tm *)
  val hastype : term * term -> term	(* tm : tm *)
  val omitobj : Paths.region -> term	(* _ as object, region for "_" *)
  val pi : dec * term -> term           (* {d} tm *)
  val lam : dec * term -> term          (* [d] tm *)
  val typ : Paths.region -> term	(* type, region for "type" *)

  (* region for "{dec}" "[dec]" etc. *)
  val dec : string option * term * Paths.region -> dec (* id : tm | _ : tm *)
  val dec0 : string option * Paths.region -> dec (* id | _  (type omitted) *)

  type condec				(* constant declaration *)
  val condec : string * term -> condec	(* id : tm *)
  val condef : string option * term * term option -> condec
					(* id : tm = tm | _ : tm = tm *)

  type query				(* query *)
  val query : string option * term -> query (* ucid : tm | tm *)

end;  (* signature EXTSYN *)

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
  val resetErrors : string -> unit      (* filename -fp *)

  type rdec = IntSyn.Dec * Paths.occExp option * Paths.region

  val ctxToCtx : dec IntSyn.Ctx -> rdec IntSyn.Ctx
  val ctxsToCtxs : dec IntSyn.Ctx list -> rdec IntSyn.Ctx list

  val termToExp : dec IntSyn.Ctx * term
                   -> rdec IntSyn.Ctx * IntSyn.Exp * IntSyn.Exp * Paths.occExp

  val queryToQuery : query * Paths.location
                     -> IntSyn.Exp * string option * (IntSyn.Exp * string) list
                     (* (A, SOME("X"), [(Y1, "Y1"),...] *)
		     (* where A is query type, X the optional proof term variable name *)
		     (* Yi the EVars in the query and "Yi" their names *)

  val condecToConDec : condec * Paths.location * bool -> IntSyn.ConDec option * Paths.occConDec option
                     (* optional ConDec is absent for anonymous definitions *)
                     (* bool = true means that condec is an abbreviation *)

  val internalInst : IntSyn.ConDec * IntSyn.ConDec * Paths.region -> IntSyn.ConDec

  val externalInst : IntSyn.ConDec * term * Paths.region -> IntSyn.ConDec

end;  (* signature TP_RECON *)
