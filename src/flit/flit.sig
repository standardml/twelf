(* Flit DAG generator *)
(* Author: Roberto Virga *)

signature FLIT =
sig

  (* init (sym_table_file) *)
  val init : string -> unit

  (* initForText () *)
  val initForText : unit -> unit

  (* dump (symbol, dag_file) *)
  val dump : (string * string) -> int

  (* dumpText (outputSemant, outputChecker) *)
  val dumpText : string * string -> unit

  (* setFlag () *)
  val setFlag : unit -> unit

  (* setEndTcb () *)
  val setEndTcb : unit -> unit

  (* dumpFlagged (dag_file) *)
  val dumpFlagged : string -> unit

  (* dumpSynTable (start_sym, end_sym, sym_table_file) *)
  val dumpSymTable : (string * string * string) -> unit

end; (* signature FLIT *)

  
