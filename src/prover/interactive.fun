(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)

functor Interactive 
  (structure Global : GLOBAL
   (*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure State' : STATE
   (*! sharing State'.IntSyn = IntSyn' !*)
   (*! sharing State'.Tomega = Tomega' !*)
   structure Formatter : FORMATTER
   structure Ring : RING
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   structure Weaken : WEAKEN
   (*! sharing Weaken.IntSyn = IntSyn' !*)
   structure ModeSyn : MODESYN
   (*! sharing ModeSyn.IntSyn = IntSyn' !*)
   structure WorldSyn : WORLDSYN
   (*! sharing WorldSyn.IntSyn = IntSyn' !*)
   (*! sharing WorldSyn.Tomega = Tomega' !*)
   structure StatePrint : STATEPRINT 
     sharing StatePrint.Formatter = Formatter
     (*! sharing StatePrint.IntSyn = IntSyn' !*)
     (*! sharing StatePrint.Tomega = Tomega' !*)
     sharing StatePrint.State = State'
   structure Introduce : INTRODUCE
   (*! sharing Introduce.IntSyn = IntSyn' !*)
   (*! sharing Introduce.Tomega = Tomega' !*)
     sharing Introduce.State = State'
   structure Split : SPLIT
   (*! sharing Split.IntSyn = IntSyn' !*)
   (*! sharing Split.Tomega = Tomega' !*)
     sharing Split.State = State'
   structure FixedPoint : FIXEDPOINT
   (*! sharing FixedPoint.IntSyn = IntSyn' !*)
   (*! sharing FixedPoint.Tomega = Tomega' !*)
     sharing FixedPoint.State = State'
   structure Fill : FILL
   (*! sharing Fill.IntSyn = IntSyn' !*)
   (*! sharing Fill.Tomega = Tomega' !*)
     sharing Fill.State = State') 
  : INTERACTIVE =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure State = State'

  exception Error = State'.Error

  local 
    structure I = IntSyn
    structure T = Tomega
    structure S = State
    structure M = ModeSyn
    structure W = WorldSyn
      

    (* this is pretty preliminary:
       I think we should just adapt the internal representation for formulas
    *)
    fun convertOneFor cid =
      let
	val V  = case I.sgnLookup cid 
	           of I.ConDec (name, _, _, _, V, I.Kind) => V
	            | _ => raise Error "Type Constant declaration expected"
	val mS = case M.modeLookup cid
	           of NONE => raise Error "Mode declaration expected"
	            | SOME mS => mS

	(* convertFor' (V, mS, w1, w2, n) = (F', F'')

	   Invariant:
	   If   G |- V = {{G'}} type :kind 
	   and  G |- w1 : G+
	   and  G+, G'+, G- |- w2 : G
	   and  G+, G'+, G- |- ^n : G+
	   and  mS is a spine for G'
	   then F'  is a formula excepting a another formula as argument s.t.
	        If G+, G'+ |- F formula,
		then . |- F' F formula 
           and  G+, G'+ |- F'' formula
	*)
	fun convertFor' (I.Pi ((D, _), V), M.Mapp (M.Marg (M.Plus, _), mS), w1, w2, n) =
            let
	      val (F', F'') = convertFor' (V, mS, I.dot1 w1, I.Dot (I.Idx n, w2), n-1)
	    in
	      (fn F => T.All (T.UDec (Weaken.strengthenDec (D, w1)), F' F), F'')
	    end
	  | convertFor' (I.Pi ((D, _), V), M.Mapp (M.Marg (M.Minus, _), mS), w1, w2, n) =
            let
	      val (F', F'') = convertFor' (V, mS, I.comp (w1, I.shift), I.dot1 w2, n+1)
	    in
	      (F', T.Ex (I.decSub (D, w2), F''))
	    end
	  | convertFor' (I.Uni I.Type, M.Mnil, _, _, _) = 
              (fn F => F, T.True)
	  | convertFor' _ = raise Error "type family must be +/- moded"

	(* shiftPlus (mS) = s'
	 
	 Invariant:
	 s' = ^(# of +'s in mS)
	 *)
	    
	fun shiftPlus mS = 
	  let
	    fun shiftPlus' (M.Mnil, n) = n
	      | shiftPlus' (M.Mapp (M.Marg (M.Plus, _), mS'), n) =
	          shiftPlus' (mS', n+1)
	      | shiftPlus' (M.Mapp (M.Marg (M.Minus, _), mS'), n) =
		  shiftPlus' (mS', n)
	  in
	    shiftPlus' (mS, 0)
	  end
	
	val n = shiftPlus mS
	val (F, F') = convertFor' (V, mS, I.id, I.Shift n, n)
      in 
	F F'
      end


    (* convertFor L = F'

       Invariant:
       If   L is a list of type families
       then F' is the conjunction of the logical interpretation of each
	    type family
     *)
    fun convertFor nil = raise Error "Empty theorem"
      | convertFor [a] = convertOneFor a
      | convertFor (a :: L) = T.And (convertOneFor a, convertFor L)
 
   (* here ends the preliminary stuff *)

    datatype MenuItem
    = Split     of Split.operator
    | Fill      of Fill.operator
    | Introduce of Introduce.operator
    | Fix       of FixedPoint.operator

    val Open : S.State Ring.ring ref = ref (Ring.init [])
    val Solved : S.State Ring.ring ref = ref (Ring.init [])
    val History : (S.State Ring.ring * S.State Ring.ring) list ref = ref nil 
    val Menu : MenuItem list option ref = ref NONE
  
    fun initOpen () = Open := Ring.init [];
    fun initSolved () = Solved := Ring.init [];
    fun empty () = Ring.empty (!Open)
    fun current () = Ring.current (!Open)
    fun delete () = Open := Ring.delete (!Open)
    fun insertOpen S = Open := Ring.insert (!Open, S)
    fun insertSolved S = Solved := Ring.insert (!Solved, S)

    fun insert S = insertOpen S

    fun collectOpen () = Ring.foldr op:: nil (!Open) 
    fun collectSolved () = Ring.foldr op:: nil (!Solved) 
    fun nextOpen () = Open := Ring.next (!Open)

    fun pushHistory () = 
	  History :=  (!Open, !Solved) :: (!History) 
    fun popHistory () = 
	case (!History)
	  of nil => raise Error "History stack empty"
	   | (Open', Solved') :: History' => 
	     (History := History';
	      Open := Open';
	      Solved := Solved')


    fun abort s =
        (print ("* " ^ s ^ "\n");
	 raise Error s)

    fun reset () = 
        (initOpen ();
	 initSolved ();
	 History := nil;
	 Menu := NONE)

    fun cLToString (nil) = ""
      | cLToString (c :: nil) = 
	  (I.conDecName (I.sgnLookup c))
      | cLToString (c :: L) = 
	  (I.conDecName (I.sgnLookup c)) ^ ", " ^ (cLToString L)

    fun IntroduceToMenu (SOME O, A) = Introduce O :: A
      | IntroduceToMenu (NONE, A) = A

    fun SplittingToMenu (nil, A) = A
      | SplittingToMenu (O :: L, A) = SplittingToMenu (L, Split O :: A)

    fun FillingToMenu (O, A) = Fill O :: A

    fun FixedPointToMenu (O, A) = Fix O :: A

    fun RecursionToMenu (O, A) = (* Recursion O :: *) A

    fun InferenceToMenu (O, A) = (* Inference O :: *) A

    fun menu () = 
	if empty () then Menu := NONE
	else 
	  let 
	    val S = current ()
	    val SplitO = Split.expand S
	    val IntroO = Introduce.expand S
	    val FixO = FixedPoint.expand S
(*	    val InfO = Inference.expand S
	    val RecO = MTPRecursion.expand S *) 
	    val FillO = Fill.expand S 
	  in
	    Menu := SOME (FillingToMenu (FillO,
			  IntroduceToMenu (IntroO, 
			  SplittingToMenu (SplitO, 
			  FixedPointToMenu (FixO, 
			  nil)))))
(*	    Menu := SOME (FillingToMenu (FillO,
					 RecursionToMenu (RecO, 
							  InferenceToMenu (InfO,
									   SplittingToMenu (SplitO, nil))))) *)
	  end




    fun format k = 
        if k < 10 then (Int.toString k) ^ ".  "
	else (Int.toString k) ^ ". "

    fun menuToString () =
	let 
	  fun menuToString' (k, nil) = ""
	    | menuToString' (k, Split O  :: M) =  
	      let 
		val s = menuToString' (k+1, M)
	      in 
		 s ^ "\n  " ^ (format k) ^ (Split.menu O)
	      end
	    | menuToString' (k, Introduce O :: M) = 
	      let 
		val s = menuToString' (k+1, M)
	      in 
		s ^ "\n  " ^ (format k) ^ (Introduce.menu O)
	      end
	    | menuToString' (k, Fill O :: M) = 
	      let 
		val s = menuToString' (k+1, M)
	      in 
		s ^ "\n  " ^ (format k) ^ (Fill.menu O)
	      end
	    | menuToString' (k, Fix O :: M) = 
	      let 
		val s = menuToString' (k+1, M)
	      in 
		s ^ "\n  " ^ (format k) ^ (FixedPoint.menu O)
	      end
(*	    | menuToString' (k, Recursion O :: M,kOopt) =
	      let 
		val (kopt, s) = menuToString' (k+1, M, kOopt)
	      in
		(kopt, s ^ "\n  " ^ (format k) ^ (MTPRecursion.menu O))
	      end
	    | menuToString' (k, Inference O :: M,kOopt) =
	      let 
		val (kopt, s) = menuToString' (k+1, M, kOopt)
	      in
		(kopt, s ^ "\n  " ^ (format k) ^ (Inference.menu O))
	      end
*)	in
	  case !Menu of 
	    NONE => raise Error "Menu is empty"
	  | SOME M =>  menuToString' (1, M)	      
	end


    fun printStats () = 
        let
	  val nopen   = Ring.foldr (fn (a, b) => b+1) 0 (!Open)
	  val nsolved = Ring.foldr (fn (a, b) => b+1) 0 (!Solved)
	in
	  (print "Statistics:\n\n";
	   print ("Number of goals : " ^ (Int.toString (nopen + nsolved)) ^"\n");
	   print ("     open goals : " ^ (Int.toString (nopen)) ^ "\n");
	   print ("   solved goals : " ^ (Int.toString (nsolved)) ^ "\n"))
	end
    fun printMenu () = 
	if empty () then (print "[QED]\n")
	else 
	  let 
	    val S = current ()
	  in 
	    (print "\n";
	     print (StatePrint.stateToString S);
	     print "\nSelect from the following menu:\n";
	     print (menuToString ());
	     print "\n")
	  end

    fun select k =
	let 
	  fun select' (k, nil) = abort ("No such menu item")
	    | select' (1, Split O :: _) = 
		let 
		  val S' = (Timers.time Timers.splitting Split.apply) O  
		  val _ = pushHistory ()
		  val _ = delete ()
		  val _ = map (fn S => insert (StatePrint.nameState S)) S'
		in
		  (menu (); printMenu ())
		end
	    | select' (1, Introduce O :: _) =
		let 
		  val S = Introduce.apply O    (* no timer yet -- cs *)
		  val _ = pushHistory ()
		  val _ = delete ()
		  val _ = insert (StatePrint.nameState S)
		in
		  (menu (); printMenu ())
		end
	    | select' (1, Fix O :: _) =
		let 
		  val S = FixedPoint.apply O    (* no timer yet -- cs *)
		  val _ = pushHistory ()
		  val _ = delete ()
		  val _ = insert (StatePrint.nameState S)
		in
		  (menu (); printMenu ())
		end
(*	    | select' (1, Recursion O :: _) = 
		let 
		  val S' = (Timers.time Timers.recursion MTPRecursion.apply) O  
		  val _ = pushHistory ()
		  val _ = delete ()
		  val _ = insert (MTPrint.nameState S')
		in
		  (menu (); printMenu ())
		end
	    | select' (1, Inference O :: _) = 
		let 
		  val S' = (Timers.time Timers.recursion Inference.apply) O  
		  val _ = pushHistory ()
		  val _ = delete ()
		  val _ = insert (MTPrint.nameState S')
		in
		  (menu (); printMenu ())
		end
*)
	    | select' (1, Fill O :: _) =
		let 
		  val S' = (Timers.time Timers.filling Fill.apply) O
		    handle Fill.Error _ =>  abort ("Filling unsuccessful: no object found")
(*		  val _ = printFillResult P *)
		  val _ = pushHistory ()
		  val _ = delete ()
		  val _ = if S.close S' then insertSolved (StatePrint.nameState S') else insert (StatePrint.nameState S')
		in
		  (menu (); printMenu ())
		end
	    | select' (k, _ :: M) = select' (k-1, M) 
	in
	  (case !Menu of 
	    NONE => raise Error "No menu defined"
	  | SOME M => select' (k, M))
	     handle S.Error s => ()
	end

    fun next () = (nextOpen (); menu (); printMenu ())

    fun undo () = (popHistory (); menu (); printMenu ())


    fun init names = 
	let 
	  val _ = reset ()
	  val cL = map (fn x => valOf (Names.constLookup (valOf (Names.stringToQid x)))) names
	  val F = convertFor cL
	  val Ws = map W.lookup cL
	  (* so far omitted:  make sure that all parts of the theorem are
	     declared in the same world 
          *)
	  val (W :: _) = Ws
	  val S = S.init (F, W)
	in
	  (insert (StatePrint.nameState S);
	   menu ();
	   printMenu ())
	end

  in
    val init = init
    val select = select
    val print = printMenu
    val stats = printStats
    val next = next
    val reset = reset
    val undo = undo
  end
end (* functor Interactive *)