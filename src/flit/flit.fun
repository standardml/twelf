(* Flit DAG generator *)
(* Author: Roberto Virga *)

functor Flit(structure Global : GLOBAL
             structure Word : WORD
             structure Pack : PACK_WORD
             structure Whnf : WHNF
             structure Names : NAMES
             structure Table : TABLE
               where type key = IntSyn.cid
             structure Index : INDEX
             structure Print : PRINT)
  : FLIT =
struct

  local
    structure W = Word
    structure I = IntSyn
    structure N = Names
    structure F = Names.Fixity
    structure Idx = Index

    exception Error of string

    val size_of_expr = 3;

    val tcb_table : (string * int) list option ref = ref NONE
    val tcb_size : int ref = ref 0

    fun print_table () =
          let
	    fun print_table' nil = ()
	      | print_table' [(name, addr)] =
	          print ("(\"" ^ name ^ "\", " ^ Int.toString addr ^ ")\n")
	      | print_table' ((name, addr) :: pairs) =
	          (print ("(\"" ^ name ^ "\", " ^ Int.toString addr ^ "),\n");
		   print_table' pairs)
          in
	    (
	      print "val tcb_table := [\n";
	      print_table' (valOf (!tcb_table));
	      print "];\n"
	    )
	  end

    fun print_size () = 
         print ("val tcb_size = " ^ Int.toString (!tcb_size) ^ ";\n")

    fun init filename =
      let
        val stream = TextIO.openIn filename

        val linecount = ref 0 : int ref;
        fun get_line () = (linecount := !linecount + 1; TextIO.inputLine stream)

        fun error () = raise Error ("Error reading file '" ^ filename
	                             ^ "', line " ^ (Int.toString (!linecount)))

        fun read_size () =
	      case (Int.fromString (get_line ()))
	        of SOME(tcb_size) => tcb_size
		 | NONE => error ()

        val () = tcb_size := read_size ()

	val () = if (!Global.chatter >= 3) then print_size () else ()

        fun read_table "" = nil
	  | read_table line =
	      case (String.tokens Char.isSpace line)
	        of [id, addr] =>
                   (id, valOf (Int.fromString addr)) :: read_table (get_line ())
                 | _ => error ()

        val () = tcb_table := SOME (read_table (get_line ()))

	val () = if (!Global.chatter >= 3) then print_table () else ()

	val () = TextIO.closeIn stream
      in
        ()
      end

    val closedMask  = LargeWord.fromInt(256);
    val predicateMask = LargeWord.fromInt(512);
    val clauseMask = LargeWord.fromInt(1024);

    val baseAddr : int ref = ref 0
    val startClause : int option ref = ref NONE;

    val tuples : int ref = ref 0
    val out : BinIO.outstream option ref = ref NONE

    val symTable : W.word Table.Table = Table.new 32
    val printTable : unit Table.Table = Table.new 32

    fun cname cid = I.conDecName (I.sgnLookup cid)

    fun clookup name =
          let
            val size = #1 (I.sgnSize ());
            fun clookup' cid =
                  if (cid = size)
                  then raise Error ("symbol " ^ name ^ " not found")
                  else if (cname cid = name)
                  then cid
                  else clookup' (cid+1)
          in
            clookup' 0
          end 

    fun print_once cid =
          case (Table.lookup printTable cid)
            of NONE => (Table.insert printTable (cid, ());
                        print (Print.conDecToString (I.sgnLookup cid) ^ "\n"))
             | SOME _ => ()

    fun print_tuple (addr, code, (cld, prd, cls), arg1, arg2) =
           print ((W.fmt StringCvt.DEC addr) ^ " : " ^
                  Char.toString code ^ "\t" ^
                  Bool.toString cld ^ "\t" ^
                  Bool.toString prd ^ "\t" ^
                  Bool.toString cls ^ "\t" ^
                  (W.fmt StringCvt.DEC arg1) ^ "\t" ^
                  (W.fmt StringCvt.DEC arg2) ^ "\n")

    fun writeArray array =
          case (!out)
            of SOME(stream) =>
                 (tuples := !tuples + 1;
                  BinIO.output (stream, Word8Array.extract (array, 0, NONE)))
             | NONE => ()
          
    fun tuple (code, flags as (cld, prd, cls), arg1, arg2) =
          let
            val addr = W.fromInt (!tuples + !tcb_size)
            val array = Word8Array.array (Pack.bytesPerElem * size_of_expr,
                                          Word8.fromInt 0)
            val opcode = ref (Word8.toLargeWord (Byte.charToByte code))
          in
	    if(cld)
            then opcode := LargeWord.orb (!opcode, closedMask)
            else ();
            if(prd)
            then opcode := LargeWord.orb (!opcode, predicateMask)
            else ();
            if(cls)
	    then opcode := LargeWord.orb (!opcode, clauseMask)
            else ();

            Pack.update (array, 0, !opcode);

            Pack.update (array, 1, W.toLargeWord arg1);
            Pack.update (array, 2, W.toLargeWord arg2);

	    if (!Global.chatter >= 4)
	    then print_tuple (addr, code, flags, arg1, arg2)
	    else ();

            writeArray array;

            addr
          end

    val kd = (fn () => W.fromInt 0)
    val ty = (fn () => W.fromInt 1)

    fun const true ty =
          tuple (#"c", (true, true, true), W.fromInt 0, ty)
      | const false _ = W.fromInt 0
       
    fun var true ty = tuple (#"v", (false, false, false), W.fromInt 0, ty)
      | var false _ = W.fromInt 0
       
    fun pi true (flags, var, exp) = tuple (#"p", flags, var, exp)
      | pi false _ = W.fromInt 0

    fun lam true (flags, var, exp) = tuple (#"l", flags, var, exp)
      | lam false _ = W.fromInt 0

    fun app true (flags, exp, arg) = tuple (#"a", flags, exp, arg)
      | app false _ = W.fromInt 0

    fun annotate true (flags, arg, exp) = tuple(#":", flags, arg, exp)
      | annotate false _ = W.fromInt 0

    fun scanNumber string =
          let
            fun check (chars as (_ :: _)) =
                 (List.all Char.isDigit chars)
              | check nil =
                  false
          in
            if check (String.explode string)
            then StringCvt.scanString (W.scan StringCvt.DEC) string
            else NONE
          end

    fun scanBinopPf oper string =
          let
            val args = String.tokens (fn c => c = oper) string
          in
            case args
              of [arg1, arg2] =>
                (case (StringCvt.scanString (W.scan StringCvt.DEC) arg1,
                       StringCvt.scanString (W.scan StringCvt.DEC) arg2)
                   of (SOME(d1), SOME(d2)) => SOME(d1, d2)
                    | _ => NONE)
               | _ => NONE
          end

    (* currently unused *)
    fun scanTernopPf oper1 oper2 string =
          let
            val args = String.tokens (fn c => c = oper1) string
          in
            case args
              of [arg1, args2] =>
          let
            val args' = String.tokens (fn c => c = oper2) args2
          in
            case args'
              of [arg2, arg3] =>
           (case (StringCvt.scanString (W.scan StringCvt.DEC) arg1,
                  StringCvt.scanString (W.scan StringCvt.DEC) arg2,
                  StringCvt.scanString (W.scan StringCvt.DEC) arg3)
                   of (SOME(d1), SOME(d2), SOME(d3)) => SOME(d1, d2, d3)
               | _ => NONE)
               | _ => NONE
          end
               | _ => NONE
          end

    fun isPredicate cid =
          case (!startClause, I.constUni cid)
            of (SOME cid', I.Kind) => (cid >= cid')
             | _ => false

    fun headCID (I.Const cid) = SOME cid
      | headCID (I.Skonst cid) = SOME cid
      | headCID (I.Def cid) = SOME cid
      | headCID (I.NSDef cid) = SOME cid
      | headCID _ = NONE

    fun isClause cid =
          case (!startClause, I.constUni cid)
            of (SOME cid', I.Type) =>
              if (cid >= cid')
              then
                let
                  val a = I.targetHead (I.constType cid)
                  val clauses = List.mapPartial headCID (Idx.lookup (valOf (headCID a)))
                in
                  List.exists (fn x => x = cid) clauses
                end
              else false
             | _ => false
          
    fun lookup cid =
          case (Table.lookup symTable cid)
            of SOME(idx) => idx
             | NONE =>
                 let
                   val idx = compileConDec (I.sgnLookup cid, (isPredicate cid, isClause cid))
                   val () = Table.insert symTable (cid, idx)
                   val () = if (!Global.chatter >= 3) then print_once cid else ()
                 in
                   idx
                 end

    and compileUni I.Kind = kd ()
      | compileUni I.Type = ty ()

    and compileExpN generate (G, I.Uni V, flags) = compileUni V
      | compileExpN generate (G, I.Pi ((I.Dec (_, U1), _), U2), flags as (cld, _, _)) =
          let
            val idxU1 = compileExpN generate (G, U1, (cld, false, false))
            val idxU1var = var generate idxU1
            val idxU2 = compileExpN generate (I.Decl (G, idxU1var), U2, (false, false, false))
          in
            pi generate (flags, idxU1var, idxU2)
          end
      | compileExpN generate (G, I.Lam (D as I.Dec (_, U1), U2), flags as (cld, _, _)) =
          let
            val idxU1 = compileExpN generate (G, U1, (cld, false, false))
            val idxU1var = var generate idxU1
            val idxU2 = compileExpN generate (I.Decl (G, idxU1var), U2, (false, false, false))
          in
            lam generate (flags, idxU1var, idxU2)
          end
      | compileExpN generate (G, U as I.Root (H, S), flags) =
          let
            val idx = compileHead generate (G, H)
          in
            compileSpine generate (G, idx, S, flags)
          end
      | compileExpN generate (G, I.FgnExp csfe, flags) =
          compileExp generate (G, I.FgnExpStd.ToInternal.apply csfe (), flags)

    and compileSpine generate (G, idx, I.Nil, flags) = idx
      | compileSpine generate (G, idx, I.App (U1, I.Nil), flags as (cld, _, _)) =
          let
            val idxU1 = compileExpN generate (G, U1, (cld, false, false))
          in
            app generate (flags, idx, idxU1)
          end
      | compileSpine generate (G, idx, I.App (U1, S), flags as (cld, _, _)) =
          let
            val idxU1 = compileExpN generate (G, U1, (cld, false, false))
          in
            compileSpine generate (G, app generate ((cld, false, false), idx, idxU1), S, flags)
          end

    and compileHead generate (G, I.BVar k) = I.ctxLookup (G, k)
      | compileHead generate (G, I.Const cid) = lookup cid
      | compileHead generate (G, I.Def cid) = lookup cid
      | compileHead generate (G, I.NSDef cid) = lookup cid
      | compileHead generate (G, I.FgnConst (cs, conDec)) = compileFgnDec generate (G, conDec)

    and compileFgnDec true (G, conDec) =
          let
            val name = I.conDecName conDec
            val flags = (true, false, false)
          in
            (case (scanNumber name)
               of SOME(n) => tuple (#"#", flags, n, W.fromInt 0)
                | NONE =>
            (case (scanBinopPf #"/" name)
               of SOME(n1, n2) => tuple (#"/", flags, n1, n2)
                | NONE =>
            (case (scanBinopPf #"+" name)
               of SOME(n1, n2) => tuple (#"+", flags, n1, n2)
                | NONE =>
            (case (scanBinopPf #"*" name)
               of SOME(n1, n2) => tuple (#"*", flags, n1, n2)
                | NONE => raise Error ("unknown foreign constant " ^ name)))))
         end
      | compileFgnDec false _ = W.fromInt 0

    and compileExp generate (G, U, flags) =
          compileExpN generate (G, Whnf.normalize (U, I.id), flags)

    and compileConDec (condec as I.ConDec (_, _, _, _, V, _), (true, cls)) =
          const true (compileExpN true (I.Null, V, (true, true, cls)))
      | compileConDec (condec as I.ConDec (_, _, _, _, _, _), (pred, cls)) =
          raise Error ("attempt to shadow constant " ^ (I.conDecName condec))
      | compileConDec (condec as I.ConDef (_, _, _, U, V, _, _), (pred, cls)) =
          let
            val exp = compileExpN true (I.Null, V, (true, false, false))
            val arg = compileExpN true (I.Null, U, (true, pred, cls))
          in
            annotate true ((true, pred, cls), arg, exp)
          end
      | compileConDec (condec as I.AbbrevDef (_, _, _, U, V, _), (pred, cls)) =
          let
            val exp = compileExpN true (I.Null, V, (true, false, false))
            val arg = compileExpN true (I.Null, U, (true, pred, cls))
          in
            annotate true ((true, pred, cls), arg, exp)
          end

    fun initTuples () =
          let
            val _ = tuples := 0
            val _ = Table.clear symTable
            val _ = Table.clear printTable
          in
            case (!tcb_table)
              of SOME(l) =>
                   List.app (fn (name, idx) =>
                             Table.insert symTable (clookup name, W.fromInt idx)) l
               | NONE => raise Error "dump(...) before init(...)"
            end

    fun dump (name, file) =
          let
            fun dump' cid =
                  let
                    val _ = out := SOME (BinIO.openOut file);
                    val stream = valOf (!out)
                    val _ = initTuples ()
                    val idx = W.toInt (lookup cid)
                    val _ = BinIO.closeOut stream
                  in
                    idx
                  end 
           fun error msg =
                 let
                   fun closeOut () =
                         case (!out)
                           of SOME (stream) => BinIO.closeOut stream
                            | NONE => ()
                 in
                   (print ("Error: " ^ msg ^ "\n"); closeOut(); ~1)
                 end 
          in
            case (N.constLookup (valOf (N.stringToQid name)))
              of SOME(cid) =>
                   (dump' cid handle Error msg => error msg)
               | NONE => error ("symbol " ^ name ^ " not found\n")
          end

    fun setFlag () =
          case (!startClause)
            of SOME(cid) => print ("Error: flag already set\n")
             | NONE => startClause := SOME(#1 (I.sgnSize ()))

    fun dumpFlagged file =
          let
            val max = #1 (I.sgnSize ())
            fun compileSeq cid =
                  if (cid < max)
                  then
                    (lookup cid;
                     compileSeq (cid + 1))
                  else ()
            fun dump' cid =
                  (out := SOME(BinIO.openOut file);
                   initTuples();
                   compileSeq cid;
                   BinIO.closeOut (valOf (!out)))
           fun error msg =
                 let
                   fun closeOut () =
                         case (!out)
                           of SOME(stream) => BinIO.closeOut stream
                            | NONE => ()
                 in
                   (print ("Error: " ^ msg ^ "\n"); closeOut())
                 end 
          in
            case (!startClause)
              of SOME (cid) =>
                   (dump' cid handle Error msg => error msg)
               | NONE => error ("setFlag() has not been called yet\n")
          end

     fun dumpSymTable (name1, name2, file) =
           let
             val stream = TextIO.openOut file
             val F.Strength nonfixLevel = F.minPrec
             fun dumpFixity cid =
                   (case (N.getFixity cid)
                      of F.Infix (F.Strength level, F.Left) => (level, 1)
                       | F.Infix (F.Strength level, F.Right) => (level, 2)
                       | F.Infix (F.Strength level, F.None) => (level, 3)
                       | F.Nonfix => (nonfixLevel, 0))
             fun dumpEntry cid =
                   (case (Table.lookup symTable cid, dumpFixity cid)
                      of (SOME(idx), (level, assoc)) =>
                           TextIO.output (stream,
                                          I.conDecName(I.sgnLookup(cid)) ^ "\t" ^
                                          (Word.fmt StringCvt.DEC idx) ^ "\t" ^
                                          Int.toString(level) ^ "\t" ^
                                          Int.toString(assoc) ^ "\n")
                       | (NONE, _) => ())
             fun dumpTable (cid1, cid2) =
                   if (cid1 <= cid2)
                   then (dumpEntry cid1; dumpTable (cid1+1, cid2))
                   else ()
             fun error msg = print ("Error: " ^ msg ^ "\n")
           in
             (case (N.constLookup (valOf (N.stringToQid name1)),
                    N.constLookup (valOf (N.stringToQid name2)))
                of (SOME(cid1), SOME(cid2)) => dumpTable (cid1, cid2)
                 | (NONE, _) => error (name1 ^ " undefined")
                 | (_, NONE) => error (name2 ^ " undefined"));
             TextIO.flushOut stream;
             TextIO.closeOut stream
           end
                     

  in
    val init = init

    val dump = dump

    val setFlag = setFlag
    val dumpFlagged = dumpFlagged

    val dumpSymTable = dumpSymTable
  end

end; (* functor Flit *)
