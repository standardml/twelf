(* Flit DAG generator *)
(* Author: Roberto Virga *)

signature FLIT =
sig

  (* init (sym_table_file) *)
  val init : string -> unit

  (* dump (symbol, dag_file) *)
  val dump : (string * string) -> int

  (* setFlag () *)
  val setFlag : unit -> unit

  (* dumpFlagged (dag_file) *)
  val dumpFlagged : string -> unit

  (* dumpSynTable (start_sym, end_sym, sym_table_file) *)
  val dumpSymTable : (string * string * string) -> unit

end; (* signature FLIT *)

  
