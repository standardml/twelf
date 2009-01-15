(* Syntax for elaborated modules *)
(* Author: Florian Rabe *)

functor ModSyn
  (structure Global : GLOBAL
   (*! structure IntSyn' : INTSYN !*)
   structure Names' : NAMES
   (*! sharing Names'.IntSyn = IntSyn' !*)
   (*! structure Paths' : PATHS !*)
   structure Origins : ORIGINS
   (*! sharing Origins.Paths = Paths' !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Strict : STRICT
   (*! sharing Strict.IntSyn = IntSyn' !*)
   structure IntTree : TABLE where type key = int
   structure HashTable : TABLE where type key = string)
  : MODSYN =
struct

  exception Error of string

end
