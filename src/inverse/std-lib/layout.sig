
(* Changes by Tom 7 in 2003- *)

(* Copyright (C) 1999-2002 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 *
 * MLton is released under the GNU General Public License (GPL).
 * Please see the file MLton-LICENSE for license information.
 *)
signature LAYOUT =
   sig

      type layout
         
      (* layout the objects on separate lines*)
      val align: layout list -> layout
      val alignPrefix: layout list * string -> layout
      val array: layout array -> layout
      (* Whether or not to print things in detail -
       * routines that create layouts should use this flag to decide
       * how detailed to print.
       *)
      val detailed: bool ref
      val empty: layout
      val ignore: 'a -> layout
      val isEmpty: layout -> bool
      (* layout the objects on separate lines, if necessary *)
      val mayAlign: layout list -> layout
      val namedRecord: string * (string * layout) list -> layout
      (* indent the entire object *)
      val indent: int -> layout -> layout
      val list: layout list -> layout
      (* give open, close, sep *)
      val listex : string -> string -> string -> layout list -> layout
          

(* (* what is this? *)
      val makeOutput: ('a -> layout) -> 'a * Outstream0.t -> unit
      val output: layout * Outstream0.t -> unit
      val outputl: layout * Outstream0.t -> unit
      val outputTree: layout * Outstream0.t -> unit
      val outputWidth: layout * int * Outstream0.t -> unit
*)

      val paren: layout -> layout
      (* print the object *)
      val print: layout * (string -> unit) -> unit
      val record: (string * layout) list -> layout
      (* give separator, ie "=" or ":" *)
      val recordex : string -> (string * layout) list -> layout

      val schemeList: layout list -> layout
      (* put string between elements *)
      val separate: layout list * string -> layout list
      (* adds string at beginning of all objects except first *)
      val separateLeft: layout list * string -> layout list
      (* adds string at the end of all objects except last *) 
      val separateRight: layout list * string -> layout list
      (* layout the objects on the same line *)
      val seq: layout list -> layout
      (* convert a string to a layout object *)
      val str: string -> layout
      val switch: {detailed: 'a -> layout, normal: 'a -> layout} -> 'a -> layout
      val tostring: layout -> string
      (* give maximum width *)
      val tostringex : int -> layout -> string
      val tuple: layout list -> layout
      val tuple2: ('a -> layout) * ('b -> layout) -> 'a * 'b -> layout
      val tuple3: ('a -> layout) * 
                  ('b -> layout) * 
                  ('c -> layout) -> 'a * 'b * 'c -> layout
      val tuple4: ('a -> layout) * 
                  ('b -> layout) * 
                  ('c -> layout) * 
                  ('d -> layout) -> 'a * 'b * 'c * 'd -> layout
      val tuple5: ('a -> layout) * 
                  ('b -> layout) * 
                  ('c -> layout) * 
                  ('d -> layout) * 
                  ('e -> layout) -> ('a * 'b * 'c * 'd * 'e) -> layout
      val vector: layout vector -> layout
   end
