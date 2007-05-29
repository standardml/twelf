(**
 A library of useful functions for everyday programming.
*) 

signature LIB = 
sig

  (** Nice for postponing an implementation. *) 
  exception Not_implemented

  (* -------------------------------------------------------------------------- *)
  (*  Booleans                                                                  *)
  (* -------------------------------------------------------------------------- *)
  
  (** Curried <code> andalso </code> *) 
  val andalso' : bool -> bool -> bool

  (** Curried <code> orelse </code> *) 
  val orelse' : bool -> bool -> bool
 
  (* -------------------------------------------------------------------------- *)
  (*  Pairs                                                                     *)
  (* -------------------------------------------------------------------------- *)

  (** First element of a pair. *)
  val fst : 'a * 'b -> 'a
  (** Second element of a pair. *)
  val snd : 'a * 'b -> 'b

  (* -------------------------------------------------------------------------- *)
  (*  Options                                                                   *)
  (* -------------------------------------------------------------------------- *)

  val is_none : 'a option -> bool
  val is_some : 'a option -> bool
  (** Get the content of an option type. 
      @exception Fail
   *)
  val the : 'a option -> 'a

  (* ------------------------------------------------------------------------- *)
  (*  Refs                                                                     *)
  (* ------------------------------------------------------------------------- *)

  (** Increment an <code> int ref <\code> *)                          
  val incr : int ref -> unit
  (** Increment an <code> int ref <\code> *)                          
  val += : int ref * int -> unit
  (** Decrement an <code> int ref <\code> *)
  val -= : int ref * int -> unit
  (** Decrement an <code> int ref <\code> *)
  val decr : int ref -> unit
  (** Prepend an element to a <code> list </code> *)
  val ::= : 'a list ref * 'a -> unit
  (** Append a list at the back of a <code> list </code> *)
  val @= : 'a list ref * 'a list -> unit

  (* -------------------------------------------------------------------------- *)
  (*  Streams                                                                   *)
  (* -------------------------------------------------------------------------- *)

  (** Infinite streams. *)
  type 'a stream

  (** Prefix of a stream, as a list *)
  val listof_s : int -> 'a stream -> 'a list
  (** 
     Select an element from a stream
     @exception Fail if there are not enough elements in the stream.
   *)
  val nth_s : int -> 'a stream -> 'a 

  (* ---------------------------------------------------------------------- *)
  (*  Functions                                                             *)
  (* ---------------------------------------------------------------------- *)

  (** Curry a function. *)
  val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
  (** Uncurry a function. *)
  val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
  (** Curry a 3 argument function.  Occasionally useful. *)
  val curry3 : ('a * 'b * 'c -> 'd) -> 'a -> 'b -> 'c -> 'd
  (** Identity combinator *)
  val id : 'a -> 'a
  (** Returns true iff a function application returns a value. *)
  val can : ('a -> 'b) -> 'a -> bool
  (** Returns true iff a function application raises an exception. *)
  val cant : ('a -> 'b) -> 'a -> bool
  (** Returns true iff a (2 argument) function application returns a value. *)
  val can2 : ('a -> 'b -> 'c) -> 'a -> 'b -> bool
  (** Curried equality *)
  val ceq : ''a -> ''a -> bool
  (** Swap the arguments of a function. *)
  val swap : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  (** Explicit application. *)
  val apply : ('a -> 'b) * 'a -> 'b
  (** Apply a function a given number of times. *)
  val repeat : ('a -> 'a) -> int -> 'a -> 'a
 
  (* -------------------------------------------------------------------------- *)
  (*  Ints                                                                      *)
  (* -------------------------------------------------------------------------- *)

  (** Add up a list of ints *)
  val sum : int list -> int
  (** max of a list of ints *)
  val max : int list -> int
  (** upto 3 5 ~~> [3,4,5] *)
  val upto : int * int -> int list
  (** @see upto *)
  val -- : int * int -> int list
  (** 3 --< 5 ~~> [3,4] *)
  val --< : int * int -> int list

  (* -------------------------------------------------------------------------- *)
  (*  Reals                                                                     *)
  (* -------------------------------------------------------------------------- *)

  (** max of a list of reals *)  
  val real_max : real list -> real
  (** sum of a list of reals *)  
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
  (** !warn = true iff <code> warning s</code> will print 
      <code> s</code> to stdout. *)
  val warn : bool ref
  (** Print a warning message to stdout.  
   @see warn
   *)
  val warning : string -> unit

  (* ---------------------------------------------------------------------- *)
  (*  Lists                                                                 *)
  (* ---------------------------------------------------------------------- *)

  (** Cons. *)
  val cons : 'a -> 'a list -> 'a list
  (** Singleton list. *)
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
                                            
  val printl : string -> unit
(*   val bracket : string -> string *)
(*   val separate : string -> string list -> string *)


end
