(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)

functor MTPi (structure MTPGlobal : MTPGLOBAL
	      structure IntSyn : INTSYN
	      structure FunSyn' : FUNSYN
		sharing FunSyn'.IntSyn = IntSyn
	      structure StateSyn' : STATESYN
		sharing StateSyn'.FunSyn = FunSyn'
	      structure MTPInit : MTPINIT
	        sharing MTPInit.FunSyn = FunSyn'
		sharing MTPInit.StateSyn = StateSyn'
  	      structure MTPFilling : MTPFILLING
	        sharing MTPFilling.StateSyn = StateSyn'
	      structure MTPSplitting : MTPSPLITTING
		sharing MTPSplitting.StateSyn = StateSyn'
	      structure MTPRecursion : MTPRECURSION
	        sharing MTPRecursion.StateSyn = StateSyn'
	      structure MTPStrategy : MTPSTRATEGY
		sharing MTPStrategy.StateSyn = StateSyn'
	      structure MTPrint : MTPRINT
		sharing MTPrint.StateSyn = StateSyn'
	      structure Names : NAMES
	        sharing Names.IntSyn = IntSyn
	      structure Timers : TIMERS
	      structure Ring : RING) 
  : MTPI =
struct
  exception Error of string

  structure FunSyn = FunSyn'
  structure StateSyn = StateSyn'

  local 
    structure I = IntSyn
    structure F = FunSyn
    structure S = StateSyn

    datatype MenuItem =
      Filling of MTPFilling.operator
    | Recursion of MTPRecursion.operator
    | Splitting of MTPSplitting.operator

    val Open : StateSyn.State Ring.ring ref = ref (Ring.init [])
    val Solved : StateSyn.State Ring.ring ref = ref (Ring.init [])
    val History : (StateSyn.State Ring.ring * StateSyn.State Ring.ring) list ref = ref nil 
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
        (print ("* " ^ s);
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

    fun SplittingToMenu (nil, A) = A
      | SplittingToMenu (O :: L, A) = SplittingToMenu (L, Splitting O :: A)

    fun FillingToMenu (O, A) = Filling O :: A

    fun RecursionToMenu (O, A) = Recursion O :: A

    fun menu () = 
	if empty () then Menu := NONE
	else 
	  let 
	    val S = current ()
	    val SplitO = MTPSplitting.expand S
	    val RecO = MTPRecursion.expand S 
	    val FillO = MTPFilling.expand S
	  in
	    Menu := SOME (FillingToMenu (FillO,
					 RecursionToMenu (RecO, 
							  SplittingToMenu (SplitO, nil))))
	  end


    fun format k = 
        if k < 10 then (Int.toString k) ^ ".  "
	else (Int.toString k) ^ ". "

    fun menuToString () =
	let 
	  fun menuToString' (k, nil) = ""
	    | menuToString' (k, Splitting O :: M) =  
		(menuToString' (k+1, M)) ^ "\n" ^ (format k) ^ (MTPSplitting.menu O)
	    | menuToString' (k, Filling O :: M) = 
		(menuToString' (k+1, M)) ^ "\n" ^ (format k) ^ (MTPFilling.menu O)
	    | menuToString' (k, Recursion O :: M) = 
		(menuToString' (k+1, M)) ^ "\n" ^ (format k) ^ (MTPRecursion.menu O)
	in
	  case !Menu of 
	    NONE => raise Error "Menu is empty"
	  | SOME M => menuToString' (1, M)
	end


(*    fun makeConDec (M.State (name, M.Prefix (G, M, B), V)) = 
	let 
	 s fun makeConDec' (I.Null, V, k) = I.ConDec (name, k, V, I.Type)
	    | makeConDec' (I.Decl (G, D), V, k) = 
	      makeConDec' (G, I.Pi ((D, I.Maybe), V), k+1)
	in
	  (makeConDec' (G, V, 0))
	end

    fun makeSignature (nil) = M.SgnEmpty
      | makeSignature (S :: SL) = 
	  M.ConDec (makeConDec S,
		      makeSignature SL)

*)
(*    fun extract () = 
	if empty () then makeSignature (collectSolved ())
	else (print "[Error: Proof not completed yet]\n"; M.SgnEmpty)
*)
    fun printMenu () = 
	if empty () then (print "[QED]\n")
	else 
	  let 
	    val S = current ()
	  in 
	    (print "\n";
	     print (MTPrint.stateToString S);
	     print "\nSelect from the following menu:\n";
	     print (menuToString ());
	     print "\n")
	  end


    fun contains (nil, _) = true
      | contains (x :: L, L') =
	  (List.exists (fn x' => x = x') L') andalso contains (L, L')

    fun equiv (L1, L2) = 
	  contains (L1, L2) andalso contains (L2, L1)

    fun init (k, FO) = 
	let 
	  val _ = MTPGlobal.maxFill := k
	  val _ = reset ();
	in
	  ((map (fn S => insert S) (MTPInit.init FO);
	    menu ();
	    printMenu ())
	   handle MTPSplitting.Error s => abort ("MTPSplitting. Error: " ^ s)
		| MTPFilling.Error s => abort ("Filling Error: " ^ s)
		| MTPRecursion.Error s => abort ("Recursion Error: " ^ s)
		| Error s => abort ("Mpi Error: " ^ s))
	end

    fun select k =
	let 
	  fun select' (k, nil) = abort ("No such menu item")
	    | select' (1, Splitting O :: _) = 
		let 
		  val S' = (Timers.time Timers.splitting MTPSplitting.apply) O  
		  val _ = pushHistory ()
		  val _ = delete ()
		  val _ = map insert S'
		in
		  (menu (); printMenu ())
		end
	    | select' (1, Recursion O :: _) = 
		let 
		  val S' = (Timers.time Timers.recursion MTPRecursion.apply) O  
		  val _ = pushHistory ()
		  val _ = delete ()
		  val _ = insert S'
		in
		  (menu (); printMenu ())
		end
	    | select' (1, Filling O :: _) =
		let 
		  val _ = 
		    case (Timers.time Timers.filling MTPFilling.apply) O of
		      false => abort ("Filling unsuccessful: no object found")
		    | true => (delete ();
			       print "\n[Subgoal finished]\n";
			       print "\n")
		in
		  (menu (); printMenu ())
		end
	    | select' (k, _ :: M) = select' (k-1, M)
	in
	  (case !Menu of 
	    NONE => raise Error "No menu defined"
	  | SOME M => select' (k, M))
	     handle MTPSplitting.Error s => abort ("MTPSplitting. Error: " ^ s)
		  | MTPFilling.Error s => abort ("Filling Error: " ^ s)
		  | MTPRecursion.Error s => abort ("Recursion Error: " ^ s)
		  | Error s => abort ("Mpi Error: " ^ s) 
	end



    fun solve () = 
	if empty () then raise Error "Nothing to prove"
	else 
	  let 
	    val S = current ()
	    val (Open', Solved') = MTPStrategy.run [S]
	      handle MTPSplitting.Error s => abort ("MTPSplitting. Error: " ^ s)
		   | MTPFilling.Error s => abort ("Filling Error: " ^ s)
		   | MTPRecursion.Error s => abort ("Recursion Error: " ^ s)
		   | Error s => abort ("Mpi Error: " ^ s) 
	    val _ = pushHistory ()
	    val _ = delete ()
	    val _ = map insertOpen Open' 
	    val _ = map insertSolved Solved'
	  in
	    (menu (); printMenu ())
	  end

    fun auto () =
	let 
	  val (Open', Solved') = MTPStrategy.run (collectOpen ())
	    handle MTPSplitting.Error s => abort ("MTPSplitting. Error: " ^ s)
		 | MTPFilling.Error s => abort ("Filling Error: " ^ s)
		 | MTPRecursion.Error s => abort ("Recursion Error: " ^ s)
		 | Error s => abort ("Mpi Error: " ^ s) 
	  val _ = pushHistory ()
	  val _ = initOpen ()
	  val _ = map insertOpen Open' 
	  val _ = map insertSolved Solved'
	in
	  (menu (); printMenu ())
	end


    fun next () = (nextOpen (); menu (); printMenu ())

    fun undo () = (popHistory (); menu (); printMenu ())

  in 
    val init = init
    val select = select
    val print = printMenu
    val next = next
    val reset = reset
    val solve = solve 
    val auto = auto
(*    val extract = extract *)
(*    val show = show *)
    val undo = undo
 end (* local *)
end; (* functor MPI *)
