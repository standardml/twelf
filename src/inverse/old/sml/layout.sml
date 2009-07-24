(* Copyright (C) 1999-2002 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 *
 * MLton is released under the GNU General Public License (GPL).
 * Please see the file MLton-LICENSE for license information.
 *)
structure Layout :> LAYOUT =
struct

(*    structure Out = Outstream0   *)

    val detailed = ref false
        
    fun switch {detailed = d,normal = n} x =
        if !detailed then d x else n x
           
    datatype t = T of {length: int,
                       tree: tree}
    and tree =
        Empty
      | String of string
      | Sequence of t list
      | Align of {force: bool, rows: t list}
      | Indent of t * int

    type layout = t

    fun length (T {length, ...}) = length
        
    val empty = T {length = 0, tree = Empty}
        
    fun isEmpty (T {length = 0, ...}) = true
      | isEmpty _ = false
        
    fun str s =
        case s of
            "" => empty
          | _ => T {length = String.size s, tree = String s}
                
    fun fold (l, b, f) = foldl f b l
        
    fun seq ts =
        let val len = fold (ts, 0, fn (t,n) => n + length t)
        in case len of
            0 => empty
          | _ => T {length = len, tree = Sequence ts}
        end

    (* XXX mayalign should do 'partial spill', so that a long list of
       short elements displays as
       [1, 2, 3
        4, 5, 6]
       
       instead of
       
       [1,
        2,
        3,
        4,
        5,
        6] *)

    local
        fun make force ts =
            let
                fun loop ts =
                    case ts of
                        [] => (ts, 0)
                      | t :: ts =>
                            let val (ts, n) = loop ts
                            in case length t of
                                0 => (ts, n)
                              | n' => (t :: ts, n + n' + 1)
                            end
                val (ts, len) = loop ts
            in case len of
                0 => empty
              | _ => T {length = len - 1, tree = Align {force = force, rows = ts}}
            end
    in
        val align = make true
        val mayAlign = make false
    end

    fun indent (t, n) = T {length = length t, tree = Indent (t, n)}
        
    val tabSize: int = 8
        
    fun K x _ = x

    fun blanks (n: int): string =
        concat [CharVector.tabulate (n div tabSize, K #"\t"),
                CharVector.tabulate (n mod tabSize, K #" ")]
        
(*
    fun outputTree (t, out) =
        let val print = Out.outputc out
            fun loop (T {tree, length}) =
                (print "(length "
                 ; print (Int.toString length)
                 ; print ")"
                 ; (case tree of
                        Empty => print "Empty"
                      | String s => (print "(String "; print s; print ")")
                      | Sequence ts => loops ("Sequence", ts)
                      | Align {force, rows} => loops ("Align", rows)
                      | Indent (t, n) => (print "(Indent "
                                          ; print (Int.toString n)
                                          ; print " "
                                          ; loop t
                                          ; print ")")))
            and loops (s, ts) = (print "("
                                 ; print s
                                 ; app (fn t => (print " " ; loop t)) ts
                                 ; print ")")
        in loop t
        end
*)    

(* doesn't include newlines. new version below - tom *)

(*
    fun tostring t =
        let
            fun loop (T {tree, ...}, accum) =
                case tree of
                    Empty => accum
                  | String s => s :: accum
                  | Sequence ts => fold (ts, accum, loop)
                  | Align {rows, ...} =>
                        (case rows of
                             [] => accum
                           | t :: ts =>
                                 fold (ts, loop (t, accum), fn (t, ac) =>
                                       loop (t, " " :: ac)))
                  | Indent (t, _) => loop (t, accum)
        in
            String.concat (rev (loop (t, [])))
        end
*)    
    fun layout_print {tree: t,
               print: string -> unit,
               lineWidth: int} =
        let
            (*val _ = outputTree (t, out)*)
            fun newline () = print "\n"
                
            fun outputCompact (t, {at, printAt}) =
                let
                    fun loop (T {tree, ...}) =
                        case tree of
                            Empty => ()
                          | String s => print s
                          | Sequence ts => app loop ts
                          | Indent (t, _) => loop t
                          | Align {rows, ...} =>
                                case rows of
                                    [] => ()
                                  | t :: ts => (loop t
                                                ; app (fn t => (print " "; loop t)) ts)
                    val at = at + length t
                in loop t
                    ; {at = at, printAt = at}
                end
            
            fun loop (t as T {length, tree}, state as {at, printAt}) =
                let
                    fun prePrint () =
                        if at >= printAt
                        then () (* can't back up *)
                        else print (blanks (printAt - at))
                in (*Out.print (concat ["at ", Int.toString at,
                * "  printAt ", Int.toString printAt,
                * "\n"]);
                *)
                    (*outputTree (t, Out.error)*)
                    case tree of
                        Empty => state
                      | Indent (t, n) => loop (t, {at = at, printAt = printAt + n})
                      | Sequence ts => fold (ts, state, loop)
                      | String s =>
                            (prePrint ()
                             ; print s
                             ; let val at = printAt + length
                               in {at = at, printAt = at}
                               end)
                      | Align {force, rows} =>
                            if not force andalso printAt + length <= lineWidth
                            then (prePrint ()
                                  ; outputCompact (t, state))
                            else (case rows of
                                      [] => state
                                    | t :: ts =>
                                          fold
                                          (ts, loop (t, state), fn (t, _) =>
                                           (newline ()
                                            ; loop (t, {at = 0, printAt = printAt}))))
                end
        in loop (tree, {at = 0, printAt = 0})
            ; ()
        end

    val defaultWidth: int = 80

    fun tostringex wid l =
        let
            val acc = ref nil : string list ref

            fun pr s = acc := s :: !acc
        in
            layout_print {tree = l, lineWidth = wid, print = pr};

            String.concat(rev (!acc))
        end

    val tostring = tostringex defaultWidth

(*
    fun outputWidth (t, width, out) =
    layout_print {tree = t,
               lineWidth = width,
               print = Out.outputc out}
*)
(*        fun output (t, out) = outputWidth (t, defaultWidth, out) *)
        val print =
            fn (t, p) => layout_print {tree = t, lineWidth = defaultWidth, print = p}

(*
    fun outputl (t, out) = (output (t, out); Out.newline out)
*)      

(*     fun makeOutput layoutX (x, out) = output (layoutX x, out)
 *)        
    fun ignore _ = empty
        
    fun separate (ts, s) =
        case ts of
            [] => []
          | t :: ts => t :: (let val s = str s
                                 fun loop [] = []
                                   | loop (t :: ts) = s :: t:: (loop ts)
                             in loop ts
                             end)
                
    fun separateLeft (ts, s) =
        case ts of
            [] => []
          | [t] => ts
          | t :: ts => t :: (map (fn t => seq [str s, t]) ts)
                
    fun separateRight (ts, s) =
        rev (let val ts = rev ts
             in case ts of
                 [] => []
               | [t] => ts
               | t :: ts => t :: (map (fn t => seq [t, str s]) ts)
             end)
        
    fun alignPrefix (ts, prefix) =
        case ts of
            [] => empty
          | t :: ts =>
                mayAlign [t, indent (mayAlign (map (fn t => seq [str prefix, t]) ts),
                                     ~ (String.size prefix))]
                
    local
        fun sequence (start, finish, sep) ts =
            seq [str start, mayAlign (separateRight (ts, sep)), str finish]
    in
        val list = sequence ("[", "]", ",")
        fun listex start finish sep = sequence (start, finish, sep)
        val schemeList = sequence ("(", ")", " ")
        val tuple = sequence ("(", ")", ",")
        fun record fts =
            sequence ("{", "}", ",")
            (map (fn (f, t) => seq [str (f ^ " = "), t]) fts)

        fun recordex sep fts =
            sequence ("{", "}", ",")
            (map (fn (f, t) => seq [str (f ^ " " ^ sep ^ " "), t]) fts)

    end

    fun vector v = tuple (Vector.foldr (op ::) [] v)

    fun array x = list (Array.foldr (op ::) [] x)

    fun namedRecord (name, fields) = seq [str name, str " ", record fields]
        
    fun paren t = seq [str "(", t, str ")"]
        
    fun tuple2 (l1, l2) (x1, x2) = tuple [l1 x1, l2 x2]
    fun tuple3 (l1, l2, l3) (x1, x2, x3) = tuple [l1 x1, l2 x2, l3 x3]
    fun tuple4 (l1, l2, l3, l4) (x1, x2, x3, x4) = tuple [l1 x1, l2 x2, l3 x3, l4 x4]
    fun tuple5 (l1, l2, l3, l4, l5) (x1, x2, x3, x4, x5) =
        tuple [l1 x1, l2 x2, l3 x3, l4 x4, l5 x5]

    val indent = fn x => fn y => indent(y, x)

end
