
signature CONTEXT =
sig
  type 'a ctx 
  exception Context of string
  val empty : 'a ctx
  val lookup : 'a ctx * int -> 'a option
  val push : 'a ctx * 'a -> 'a ctx
  val list : 'a ctx -> 'a list
end

