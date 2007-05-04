
signature LIB = 
sig

  exception Failure of string
  exception Not_implemented

  val failwith : string -> exn

  (* -------------------------------------------------------------------------- *)
  (*  Booleans                                                                  *)
  (* -------------------------------------------------------------------------- *)
  
  val andalso' : bool -> bool -> bool
  val orelse' : bool -> bool -> bool
 
  (* -------------------------------------------------------------------------- *)
  (*  Pairs                                                                     *)
  (* -------------------------------------------------------------------------- *)

  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b

  (* -------------------------------------------------------------------------- *)
  (*  Options                                                                   *)
  (* -------------------------------------------------------------------------- *)

  val is_none : 'a option -> bool
  val is_some : 'a option -> bool
  val the : 'a option -> 'a

  (* ------------------------------------------------------------------------- *)
  (*  Refs                                                                     *)
  (* ------------------------------------------------------------------------- *)

  val += : int ref * int -> unit
  val -= : int ref * int -> unit
  val incr : int ref -> unit
  val decr : int ref -> unit
  val ::= : 'a list ref * 'a -> unit
  val @= : 'a list ref * 'a list -> unit

  (* -------------------------------------------------------------------------- *)
  (*  Streams                                                                   *)
  (* -------------------------------------------------------------------------- *)

  type 'a stream

  val listof_s : int -> 'a stream -> 'a list
  val nth_s : int -> 'a stream -> 'a (* raises Failure if not enough elements *)

  (* ---------------------------------------------------------------------- *)
  (*  Functions                                                             *)
  (* ---------------------------------------------------------------------- *)

  val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
  val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
  val curry3 : ('a * 'b * 'c -> 'd) -> 'a -> 'b -> 'c -> 'd
  val id : 'a -> 'a
  val can : ('a -> 'b) -> 'a -> bool
  val cant : ('a -> 'b) -> 'a -> bool
  val can2 : ('a -> 'b -> 'c) -> 'a -> 'b -> bool
  val ceq : ''a -> ''a -> bool
  val swap : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  val apply : ('a -> 'b) * 'a -> 'b
  val repeat : ('a -> 'a) -> int -> 'a -> 'a
 
  (* -------------------------------------------------------------------------- *)
  (*  Ints                                                                      *)
  (* -------------------------------------------------------------------------- *)

  val sum : int list -> int
  val max : int list -> int
  val upto : int * int -> int list
  val -- : int * int -> int list
  val --< : int * int -> int list

  (* -------------------------------------------------------------------------- *)
  (*  Reals                                                                     *)
  (* -------------------------------------------------------------------------- *)

  val real_max : real list -> real
  val real_sum : real list -> real

  (* ------------------------------------------------------------------------- *)
  (*  Order                                                                    *)
  (* ------------------------------------------------------------------------- *)

  val string_ord : string * string -> order
  val int_ord : int * int -> order
  val lex_ord : ('a * 'b -> order) -> ('c * 'd -> order) -> ('a * 'c) * ('b * 'd) -> order
  val eq_ord : ''a * ''a -> order

  (* ---------------------------------------------------------------------- *)
  (*  Debug                                                                 *)
  (* ---------------------------------------------------------------------- *)
 
  val assert : bool -> string -> unit
  val warn : bool ref
  val warning : string -> unit

  (* ---------------------------------------------------------------------- *)
  (*  Lists                                                                 *)
  (* ---------------------------------------------------------------------- *)

  val cons : 'a -> 'a list -> 'a list
  val list : 'a -> 'a list
  val itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val citlist : ('a * 'b -> 'b) -> 'a list -> 'b -> 'b
  val ith : int -> 'a list -> 'a
  val map2 : ('a * 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val map3 : ('a * 'b * 'c -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list
  val zip : 'a list -> 'b list -> ('a * 'b) list
  val zip3 : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list
  val zip4 : 'a list -> 'b list -> 'c list -> 'd list -> ('a * 'b * 'c * 'd) list
  val zip5 : 'a list -> 'b list -> 'c list -> 'd list -> 'e list -> ('a * 'b * 'c * 'd * 'e) list
  val unzip : ('a * 'b) list -> 'a list * 'b list
  val unzip3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
  val unzip4 : ('a * 'b * 'c * 'd) list -> 'a list * 'b list * 'c list * 'd list
  val ~~ : 'a list * 'b list -> ('a * 'b) list
  val end_itlist : ('a -> 'a -> 'a) -> 'a list -> 'a
  val end_citlist : ('a * 'a -> 'a) -> 'a list -> 'a
  val itlist2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
  val rev_itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val rev_end_itlist : ('a -> 'a -> 'a) -> 'a list -> 'a
  val replicate : 'a -> int -> 'a list
  val exists : ('a -> bool) -> 'a list -> bool
  val forall : ('a -> bool) -> 'a list -> bool
  val last : 'a list -> 'a
  val butlast : 'a list -> 'a list
  val gen_list_eq : ('a * 'b -> order) -> 'a list -> 'b list -> bool
  val list_eq : ''a list -> ''a list -> bool
  val partition : ('a -> bool) -> 'a list -> 'a list * 'a list
  val filter : ('a -> bool) -> 'a list -> 'a list
  val sort : ('a * 'a -> order) -> 'a list -> 'a list
  val uniq : ('a * 'a -> order) -> 'a list -> 'a list
  val uniq_list : ('a * 'a -> order) -> 'a list -> bool
  val split_at : int -> 'a list -> 'a list * 'a list
  val list_prefix : int -> 'a list -> 'a list
  val list_slice : int -> int -> 'a list -> 'a list
  val shuffle : 'a list -> 'a list -> 'a list
  val find_index : ('a -> bool) -> 'a list -> int option
  val index : ''a -> ''a list -> int option
  val find_last_index : ('a -> bool) -> 'a list -> int option
  val last_index : ''a -> ''a list -> int option
  val flatten : 'a list list -> 'a list
  val chop_list : int -> 'a list -> 'a list * 'a list
  val list_to_string : ('a -> string) -> 'a list -> string
  val remove : ('a -> bool) -> 'a list -> 'a * 'a list
  val do_list : ('a -> 'b) -> 'a list -> unit
  val exn_index : ('a -> 'b) -> 'a list -> int option

  (* ------------------------------------------------------------------------- *)
  (*  Lists as Sets                                                            *)
  (* ------------------------------------------------------------------------- *)

  val gen_setify : ('a * 'a -> order) -> 'a list -> 'a list
  val setify : ''a list -> ''a list
  val gen_mem : ('a * 'b -> order) -> 'a -> 'b list -> bool
  val mem : ''a -> ''a list -> bool
  val insert : ''a -> ''a list -> ''a list
  val gen_disjoint : ('a * 'b -> order) -> 'a list -> 'b list -> bool
  val disjoint : ''a list -> ''a list -> bool
  val gen_pairwise_disjoint : ('a * 'a -> order) -> 'a list list -> bool
  val pairwise_disjoint : ''a list list -> bool
  val gen_set_eq : ('a * 'a -> order) -> 'a list -> 'a list -> bool
  val diff : ''a list -> ''a list -> ''a list
  val union : ''a list -> ''a list -> ''a list
  val unions : ''a list list -> ''a list
  val intersect : ''a list -> ''a list -> ''a list
  val subtract : ''a list -> ''a list -> ''a list
  val subset : ''a list -> ''a list -> bool
  val set_eq : ''a list -> ''a list -> bool

  (* ------------------------------------------------------------------------- *)
  (*  Assoc lists                                                              *)
  (* ------------------------------------------------------------------------- *)

  val find : ('a -> bool) -> 'a list -> 'a option
  val assoc : ''a -> (''a * 'b) list -> 'b option
  val rev_assoc : ''a -> ('b * ''a) list -> 'b option

  (* -------------------------------------------------------------------------- *)
  (*  Printing                                                                  *)
  (* -------------------------------------------------------------------------- *)
                                            
(*   val bracket : string -> string *)
(*   val separate : string -> string list -> string *)


end
