
signature SIGNAT =
sig
  type key
  type 'a sgn
  exception Signat of string
  val empty : unit -> 'a sgn
  val insert : 'a sgn -> key * 'a -> 'a sgn (* raises Signat if key is not fresh*)
  val lookup : 'a sgn -> key -> 'a (* raises Signat if not present *)
  val size : 'a sgn -> int
end

structure ListSignat : SIGNAT where type key = int =
struct 

  structure L = Lib
  type key = int
  type 'a sgn = (key * 'a) list

  exception Signat of string
                      
  fun empty() = []

  fun insert sgn (p as (k,a)) = 
      if L.exists (fn (k',_) => k = k') sgn
      then raise Signat "insert: signat contains key"
      else p::sgn

  fun lookup sgn x = 
      case L.assoc x sgn of 
        SOME y => y
      | NONE => raise Signat "lookup: no such key"

  fun size l = length l

end

structure GrowarraySignat : SIGNAT where type key = int =
struct
  
  structure L = Lib
  structure G = GrowArray

  type key = int
  type 'a sgn = {arr : 'a G.growarray,
                 size : int ref}

  exception Signat of string
                      
  val size = ref 0

  fun empty() = {arr = G.empty(),
                 size = ref 0}

  fun insert (sgn:('a sgn)) (n,v) =
      if G.length (#arr sgn) > n
      then raise Signat "insert: signat contains key"
      else
        (G.update (#arr sgn) n v;
         (if n > !(#size sgn) then (#size sgn) := n else ());
         sgn)

  fun lookup (sgn:'a sgn) n = G.sub (#arr sgn) n

  fun size (sgn:'a sgn) = !(#size sgn)

end

structure Signat = GrowarraySignat
