
structure Lib :> LIB =
struct

  nonfix upto mem ins union subset mod div
  infix ~~ -- += -= ::= @= oo ooo oooo
 
  exception Not_implemented

  (* ------------------------------------------------------------------------- *)
  (*  Booleans                                                                 *)
  (* ------------------------------------------------------------------------- *)

  fun andalso' x y = x andalso y
  fun orelse' x y = x orelse y

  (* ---------------------------------------------------------------------- *)
  (*  Pairs                                                                 *)
  (* ---------------------------------------------------------------------- *)

  fun fst (x,y) = x
  fun snd (x,y) = y

  (* -------------------------------------------------------------------------- *)
  (*  Options                                                                   *)
  (* -------------------------------------------------------------------------- *)

  fun is_none NONE = true
    | is_none (SOME _) = false
  fun is_some NONE = false
    | is_some (SOME _) = true
  fun the NONE = raise Fail "the"
    | the (SOME x) = x

  (* ------------------------------------------------------------------------- *)
  (*  Refs                                                                     *)
  (* ------------------------------------------------------------------------- *)

  fun x += n = x := (!x) + n
  fun x -= n = x := (!x) - n
  fun incr x = x += 1
  fun decr x = x -= 1
  fun l ::= v = l := v::(!l)
  fun l @= l' = l := (!l) @ l'

  (* -------------------------------------------------------------------------- *)
  (*  Streams                                                                   *)
  (* -------------------------------------------------------------------------- *)

  datatype 'a stream = SNil 
                     | SCons of unit -> 'a * 'a stream

  fun constant_s x = SCons (fn () => (x,(constant_s x)))

  fun ones_f n = SCons (fn () => (n,(ones_f (n + 1))))

  val nat_s = ones_f 0

  fun nth_s n SNil = raise Fail "s_nth"
    | nth_s 0 (SCons f) = fst(f())
    | nth_s n (SCons f) = let val (_,s') = f() in nth_s (n - 1) s' end

  fun listof_s 0 _ = []
    | listof_s n SNil = raise Fail "listof_s"
    | listof_s n (SCons f) = let val (v,s) = f() in v::listof_s (n - 1) s end

  (* ---------------------------------------------------------------------- *)
  (*  Functions                                                             *)
  (* ---------------------------------------------------------------------- *)

  fun curry f x y = f(x,y)
  fun uncurry f (x,y) = f x y
  fun curry3 f x y z = f(x,y,z)
  fun id x = x  
  fun can f x = (f x;true) handle _ => false
  fun cant f x = (f x;false) handle _ => true
  fun can2 f x y = (f x y;true) handle _ => false
  fun ceq x y = x = y
  fun (f oo g) x y = f (g x y)
  fun (f ooo g) x y z = f (g x y z)
  fun (f oooo g) x y z w = f (g x y z w)
  fun swap f x y = f y x
  fun apply(f,x) = f x
  fun repeat f n x = if n = 0 then x else repeat f (n - 1) (f x)
 
  (* -------------------------------------------------------------------------- *)
  (*  Ints                                                                      *)
  (* -------------------------------------------------------------------------- *)

  fun max xs = foldr Int.max 0 xs
  fun sum ns = foldr op+ 0 ns
  fun uptoby k m n = if m > n then [] else m::(uptoby k (m + k) n)
  val upto = uncurry(uptoby 1)
  val op-- = upto
  infix --<
  fun x --< y = x -- (y - 1)
  
  fun pow x n = 
      case n of 
        0 => 1
      | n => if Int.mod(n,2) = 0 then 
               let val n' = pow x (Int.div(n,2)) in n' * n' end
             else x * pow x (n - 1)

  fun log n = 
      let
        fun log n even = 
            case n of 
              1 => (0,even)
            | n => 
              let
                val (ln,even') = log (Int.div(n,2)) even
                val even'' = even' andalso (Int.mod(n,2) = 0)
              in
                (1 + ln,even'')
              end
      in
        log n true
      end

  (* -------------------------------------------------------------------------- *)
  (*  Reals                                                                     *)
  (* -------------------------------------------------------------------------- *)

  fun real_max xs = foldr Real.max 0.0 xs
  fun real_sum rs = foldr op+ 0.0 rs

  (* ------------------------------------------------------------------------- *)
  (*  Order                                                                    *)
  (* ------------------------------------------------------------------------- *)

  fun string_ord (s1:string,s2) = 
      if s1 < s2 then LESS else if s1 = s2 then EQUAL else GREATER

  fun int_ord (s1:int,s2) = 
      if s1 < s2 then LESS else if s1 = s2 then EQUAL else GREATER

  fun lex_ord o1 o2 ((x1,y1),(x2,y2)) =
      case o1(x1,x2) of 
        EQUAL => o2(y1,y2)
      | x => x

  fun eq_ord(x,y) = if x = y then EQUAL else LESS

  (* ---------------------------------------------------------------------- *)
  (*  Debug                                                                 *)
  (* ---------------------------------------------------------------------- *)
 
  fun assert b s = if b then () else raise Fail ("Assertion Failure: " ^ s)
  
  val warn = ref true
  fun warning s = if !warn then TextIO.print ("Warning: " ^ s ^ "\n") else ()

  (* ---------------------------------------------------------------------- *)
  (*  Lists                                                                 *)
  (* ---------------------------------------------------------------------- *)

  fun list x = [x]

  fun cons x xs = x::xs

  (* same as foldr *)
  fun itlist f [] b = b
    | itlist f (h::t) b = f h (itlist f t b)

  fun citlist f l b = itlist (curry f) l b

  fun ith i [] = raise Fail "ith: empty"
    | ith 0 (h::t) = h
    | ith n (h::t) = ith (n-1) t

  fun map2 f [] [] = []
    | map2 f (h1::t1) (h2::t2) = 
      f(h1,h2)::map2 f t1 t2
    | map2 f _ _ = raise Fail "map2: length mismatch"

  fun map3 f [] [] [] = []
    | map3 f (h1::t1) (h2::t2) (h3::t3) = f(h1,h2,h3)::map3 f t1 t2 t3
    | map3 f _ _ _= raise Fail "map3: unequal lengths"

  fun map4 f [] [] [] [] = []
    | map4 f (h1::t1) (h2::t2) (h3::t3) (h4::t4) = f(h1,h2,h3,h4)::map4 f t1 t2 t3 t4
    | map4 f _ _ _ _ = raise Fail "map4: unequal lengths"

  fun map5 f [] [] [] [] [] = []
    | map5 f (h1::t1) (h2::t2) (h3::t3) (h4::t4) (h5::t5) = f(h1,h2,h3,h4,h5)::map5 f t1 t2 t3 t4 t5
    | map5 f _ _ _ _ _ = raise Fail "map5: unequal lengths"

  fun zip l1 l2 = map2 id l1 l2
  fun zip3 l1 l2 l3 = map3 id l1 l2 l3
  fun zip4 l1 l2 l3 l4 = map4 id l1 l2 l3 l4
  fun zip5 l1 l2 l3 l4 l5 = map5 id l1 l2 l3 l4 l5

  fun unzip l = itlist (fn (h1,h2) => fn (t1,t2) => (h1::t1,h2::t2)) l ([],[])  
  fun unzip3 l = itlist (fn (h1,h2,h3) => fn (t1,t2,t3) => (h1::t1,h2::t2,h3::t3)) l ([],[],[])  
  fun unzip4 l = itlist (fn (h1,h2,h3,h4) => fn (t1,t2,t3,t4) => (h1::t1,h2::t2,h3::t3,h4::t4)) l ([],[],[],[])  

  fun x ~~ y = zip x y

  fun end_itlist f [] = raise Fail "end_itlist"
    | end_itlist f [x] = x
    | end_itlist f (h::t) = f h (end_itlist f t)

  fun end_citlist f l = end_itlist (curry f) l

  fun itlist2 f [] [] b = b
    | itlist2 f (h1::t1) (h2::t2) b = f h1 h2 (itlist2 f t1 t2 b)
    | itlist2 _ _ _ _ = raise Fail "itlist2"

  (* same as foldl *)
  fun rev_itlist f [] b = b
    | rev_itlist f (h::t) b = rev_itlist f t (f h b)

  fun rev_end_itlist f [] = raise Fail "rev_end_itlist"
    | rev_end_itlist f [x] = x
    | rev_end_itlist f (h::t) = f (rev_end_itlist f t) h 

  fun replicate x 0 = []
    | replicate x n = if n > 0 then x::replicate x (n-1) else []

  fun exists f [] = false
    | exists f (h::t) = f h orelse exists f t

  fun forall f [] = true
    | forall f (h::t) = f h andalso forall f t

  fun last [] = raise Fail "Last"
    | last (h::[]) = h
    | last (h::t) = last t

  fun butlast [] = raise Fail "Butlast"
    | butlast (h::[]) = []
    | butlast (h::t) = h::butlast t

  fun gen_list_eq ord l1 l2 = 
      itlist2 (fn x => fn y => fn z => ord(x,y) = EQUAL andalso z) l1 l2 true 

  fun list_eq l1 l2 = gen_list_eq eq_ord l1 l2

  fun partition p [] = ([],[])
    | partition p (h::t) = 
      let 
        val (l,r) = partition p t 
      in
        if p h then (h::l,r) else (l,h::r)
      end

  fun filter p l = fst (partition p l)

  fun sort ord [] = []
    | sort ord (piv::rest) =
      let 
        val (l,r) = partition (fn x => ord(x,piv) = LESS) rest 
      in
        (sort ord l) @ (piv::(sort ord r))
      end

  fun uniq ord (x::(t as y::_)) = 
      let 
        val t' = uniq ord t
      in
        if ord(x,y) = EQUAL then t' else x::t'
      end
    | uniq _ l = l

  fun uniq_list comp l = length (uniq comp l) = length l

  fun split_at _ [] = raise Fail "split_at: splitting empty"
    | split_at 0 l = ([],l)
    | split_at n (xs as x::ys) =
      if n < 0 then raise Fail "split_at: arg out of range" else
      let val (ps,qs) = split_at (n-1) ys in (x::ps,qs) end

  fun list_prefix n l = fst (split_at n l)
                        handle Fail _ => raise Fail "list_prefix"

  fun list_slice n m l = 
      let
        val (_,r) = split_at n l
        val (l',_) = split_at m r
      in
        l'
      end

  fun shuffle [] l2 = l2
    | shuffle l1 [] = l1
    | shuffle (h1::t1) (h2::t2) = h1::h2::shuffle t1 t2

  fun find_index p =
      let 
        fun ind n [] = NONE
          | ind n (h::t) = if p h then SOME n else ind (n + 1) t 
      in
        ind 0
      end

  fun index x l = find_index (ceq x) l 

  fun find_last_index p l = 
      let
        val n = length l
        val l' = rev l
      in
        case find_index p l' of 
          SOME n' => SOME(n - n' - 1)
        | NONE => NONE
      end

  fun last_index x l = find_last_index (ceq x) l

  fun flatten l = itlist (curry op@) l []

  fun chop_list 0 l = ([],l)
    | chop_list n l = 
      let val (l1,l2) = chop_list (n-1) (tl l) in (hd l::l1,l2) end
        handle _ => raise Fail "chop_list"

  fun list_to_string f l = 
      let
        val l' = map f l
      in
        itlist (fn x => fn y => x ^ "," ^ y) ("["::l'@["]"]) ""
      end

  fun remove p [] = raise Fail "remove"
    | remove p (h::t) = 
      if p h then (h,t) else
      let val (y,n) = remove p t in (y,h::n) end

  fun do_list f [] = ()
    | do_list f (h::t) = (f h; do_list f t)

  fun exn_index f l = 
      let
        fun exn_index f [] n = NONE
          | exn_index f (h::t) n = if can f h then exn_index f t (n + 1) else SOME n
      in
        exn_index f l 0
      end

  (* ------------------------------------------------------------------------- *)
  (*  Lists as Sets                                                            *)
  (* ------------------------------------------------------------------------- *)

  fun gen_setify ord s = uniq ord (sort ord s)
  fun setify s = gen_setify eq_ord s

  fun gen_mem ord x [] = false
    | gen_mem ord x (h::t) = if ord(x,h) = EQUAL then true else gen_mem ord x t

  fun mem x l = gen_mem eq_ord x l

  fun insert x l = if mem x l then l else x::l

  fun gen_disjoint ord l1 l2 = forall (fn x => not (gen_mem ord x l2)) l1

  fun disjoint l = gen_disjoint eq_ord l

  fun gen_pairwise_disjoint p [] = true
    | gen_pairwise_disjoint p (h::t) = 
      forall (gen_disjoint p h) t andalso gen_pairwise_disjoint p t

  fun pairwise_disjoint t = gen_pairwise_disjoint eq_ord t
 
  fun gen_set_eq ord l1 l2 = gen_list_eq ord (gen_setify ord l1) (gen_setify ord l2)

  fun diff [] l = []
    | diff (h::t) l = if mem h l then diff t l else h::diff t l  

  fun union l1 l2 = itlist insert l1 l2

  fun unions l = itlist union l []

  fun intersect l1 l2 = filter (fn x => mem x l2) l1

  fun subtract l1 l2 = filter (fn x => not (mem x l2)) l1

  fun subset l1 l2 = forall (fn t => mem t l2) l1

  fun set_eq l1 l2 = subset l1 l2 andalso subset l2 l1

  (* ------------------------------------------------------------------------- *)
  (*  Assoc lists                                                              *)
  (* ------------------------------------------------------------------------- *)

  fun find p [] = NONE
    | find p (h::t) = if p h then SOME h else find p t;;

  fun assoc x l = 
      case find (fn p => fst p = x) l of
        SOME (x,y) => SOME y 
      | NONE => NONE

  fun rev_assoc x l = 
      case find (fn p => snd p = x) l of
        SOME (x,y) => SOME x
      | NONE => NONE

  (* ------------------------------------------------------------------------- *)
  (*  Strings                                                                  *)
  (* ------------------------------------------------------------------------- *)

  fun char_max c1 c2 = if Char.ord c1 < Char.ord c2 then c1 else c2

  fun string_lt (x:string) y = x < y

  fun collect l = itlist (curry op^)  l ""

  fun commas n = replicate "," n

  fun shuffle_commas l = shuffle l (commas (length l - 1))

  fun semis n = replicate ";" n

  fun parenify x = collect ["(",x,")"]

  fun postfix n s = substring(s,size s - n, n)

  val numeric_chars = "0123456789"
  val lowercase_chars = "abcdefghijklmnopqrstuvwxyz"
  val uppercase_chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
  val alpha_chars = lowercase_chars ^ uppercase_chars
  val alphanum_chars = alpha_chars ^ numeric_chars
  val word_sym_chars = "_'"
  val word_chars = alphanum_chars ^ word_sym_chars

  val explode = String.explode

  local 
    fun is_legal u s = forall (fn x => mem x (explode u)) (explode s)
  in
    val is_numeric = is_legal numeric_chars
    val is_lower = is_legal lowercase_chars
    val is_upper = is_legal uppercase_chars
    val is_alpha = is_legal alpha_chars
    val is_alnum = is_legal alphanum_chars 
    val is_word_sym = is_legal word_sym_chars
    val is_word = is_legal word_chars
  end

  val to_lower = String.translate (Char.toString o Char.toLower)
  val to_upper = String.translate (Char.toString o Char.toUpper)
  
  fun capitalize s = 
      case map Char.toString (explode s) of
        [] => ""
      | h::t => concat ([to_upper h] @ (map to_lower t))

  val newline = Char.toString #"\n"

  fun ends_with s e = 
      substring(s,size s - size e,size e) = e
      handle _ => false

  fun starts_with s e = 
      substring(s,0,size e) = e
      handle _ => false

  (* abc.def.ghi -> (abc,def.ghi) *)
  fun strip_path c s =
      let
        val n = case index c (String.explode s) of
                  SOME x => x
                | NONE => raise Fail "strip_path"
        val m = substring(s,0,n)
        val m' = substring(s,n+1,size s - n - 1)
      in
        (m,m')
      end

  (* abc.def.ghi -> (abc.def,ghi) *)
  fun rev_strip_path c s =
      let
        val no = last_index c (String.explode s)
        val n = case no of SOME x => x | NONE => raise Fail "rev_strip_path"
        val m = substring(s,0,n)
        val m' = substring(s,n+1,size s - n - 1)
      in
        (m,m')
      end

  (* ------------------------------------------------------------------------- *)
  (*  Options                                                                  *)
  (* ------------------------------------------------------------------------- *)

  fun the (SOME x) = x
    | the _ = raise Fail "the"

  fun is_some (SOME _) = true
    | is_some _ = false

  fun is_none NONE = true
    | is_none _ = false

  fun list_of_opt_list [] = []
    | list_of_opt_list (NONE::t) = list_of_opt_list t
    | list_of_opt_list (SOME x::t) = x::list_of_opt_list t

  fun get_opt (SOME x) _ = x
    | get_opt NONE err = raise Fail err

  fun get_list (SOME l) = l
    | get_list NONE = []

  fun conv_opt f (SOME l) = SOME (f l)
    | conv_opt f NONE = NONE

  (* ------------------------------------------------------------------------- *)
  (*  Timing                                                                   *)
  (* ------------------------------------------------------------------------- *)

  fun time f x = 
      let
        val timer = Timer.startCPUTimer()
      in
        let
          val res = f x 
          val time = Timer.checkCPUTimer timer
          val _ = print ("CPU time (user): " ^ Time.toString (#usr time))
        in
          res
        end
          handle e => 
                 let
                   val time = Timer.checkCPUTimer timer
                 in
                   print ("Failed after (user) CUP time of " ^ Time.toString (#usr time));
                   raise e
                 end

      end

  (* ------------------------------------------------------------------------- *)
  (*  IO                                                                       *)
  (* ------------------------------------------------------------------------- *)

  fun printl s = print (s ^ "\n")

  fun read_file file = 
      let
        val f = TextIO.openIn file
        val s = TextIO.inputAll f
        val _ = TextIO.closeIn f
      in
        s
      end

  fun write_file file s = 
      let
        val f = TextIO.openOut file
        val _ = TextIO.output(f,s)
        val _ = TextIO.closeOut f
      in
        ()
      end

  fun write_file_append file s = 
      let
        val f = TextIO.openAppend file
        val _ = TextIO.output(f,s)
        val _ = TextIO.closeOut f
      in
        ()
      end

  fun all_dir_files dir = 
      let
        val str = OS.FileSys.openDir dir
        val fs = ref []
        val f = ref (OS.FileSys.readDir str)
      in
        (while !f <> NONE do
          (fs ::= the (!f);
           f := OS.FileSys.readDir str));
        !fs
      end


end
