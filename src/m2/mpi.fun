(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)

functor Mpi (structure MetaGlobal : METAGLOBAL
             structure MetaSyn' : METASYN
             structure Init : INIT
             sharing Init.MetaSyn = MetaSyn'
             structure Filling : FILLING
             sharing Filling.MetaSyn = MetaSyn'
             structure Splitting : SPLITTING
             sharing Splitting.MetaSyn = MetaSyn'
             structure Recursion : RECURSION
             sharing Recursion.MetaSyn = MetaSyn'
             structure Lemma : LEMMA
             sharing Lemma.MetaSyn = MetaSyn'
             structure Strategy : STRATEGY
             sharing Strategy.MetaSyn = MetaSyn'
             structure Qed : QED
             sharing Qed.MetaSyn = MetaSyn'
             structure MetaPrint : METAPRINT
             sharing MetaPrint.MetaSyn = MetaSyn'
             structure Names : NAMES
             (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
             structure Timers : TIMERS
             structure Ring : RING)
  : MPI =
struct
  structure MetaSyn = MetaSyn'

  exception Error of string

  local
    structure M = MetaSyn
    structure I = IntSyn

    datatype MenuItem =
      Filling of Filling.operator
    | Recursion of Recursion.operator
    | Splitting of Splitting.operator

    val Open : MetaSyn.State Ring.ring ref = ref (Ring.init [])
    val Solved : MetaSyn.State Ring.ring ref = ref (Ring.init [])
    val History : (MetaSyn.State Ring.ring * MetaSyn.State Ring.ring) list ref = ref nil
    val Menu : MenuItem list option ref = ref NONE

    fun initOpen () = Open := Ring.init [];
    fun initSolved () = Solved := Ring.init [];
    fun empty () = Ring.empty (!Open)
    fun current () = Ring.current (!Open)
    fun delete () = Open := Ring.delete (!Open)
    fun insertOpen S = Open := Ring.insert (!Open, S)
    fun insertSolved S = Solved := Ring.insert (!Solved, S)

    fun insert S =
        if Qed.subgoal S then
          (insertSolved S;
           print (MetaPrint.stateToString S);
           print "\n[Subgoal finished]\n";
           print "\n")
        else insertOpen S

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

    fun FillingToMenu (nil, A) = A
      | FillingToMenu (O :: L, A) = FillingToMenu (L, Filling O :: A)

    fun RecursionToMenu (nil, A) = A
      | RecursionToMenu (O :: L, A) = RecursionToMenu (L, Recursion O :: A)

    fun menu () =
        if empty () then Menu := NONE
        else
          let
            val S = current ()
            val SplitO = Splitting.expand S
            val  RecO = Recursion.expandEager S
            val (FillO, FillC) = Filling.expand S
          in
            Menu := SOME (FillingToMenu ([FillC],
                          FillingToMenu (FillO,
                                         RecursionToMenu (RecO,
                                                          SplittingToMenu (SplitO, nil)))))
          end


    fun format k =
        if k < 10 then (Int.toString k) ^ ".  "
        else (Int.toString k) ^ ". "

    fun menuToString () =
        let
          fun menuToString' (k, nil) = ""
            | menuToString' (k, Splitting O :: M) =
                (menuToString' (k+1, M)) ^ "\n" ^ (format k) ^ (Splitting.menu O)
            | menuToString' (k, Filling O :: M) =
                (menuToString' (k+1, M)) ^ "\n" ^ (format k) ^ (Filling.menu O)
            | menuToString' (k, Recursion O :: M) =
                (menuToString' (k+1, M)) ^ "\n" ^ (format k) ^ (Recursion.menu O)
        in
          case !Menu of
            NONE => raise Error "Menu is empty"
          | SOME M => menuToString' (1, M)
        end


    fun makeConDec (M.State (name, M.Prefix (G, M, B), V)) =
        let
          fun makeConDec' (I.Null, V, k) = I.ConDec (name, NONE, k, I.Normal, V, I.Type)
            | makeConDec' (I.Decl (G, D), V, k) =
              makeConDec' (G, I.Pi ((D, I.Maybe), V), k+1)
        in
          (makeConDec' (G, V, 0))
        end

    fun makeSignature (nil) = M.SgnEmpty
      | makeSignature (S :: SL) =
          M.ConDec (makeConDec S,
                      makeSignature SL)
    fun extract () =
        if empty () then makeSignature (collectSolved ())
        else (print "[Error: Proof not completed yet]\n"; M.SgnEmpty)

    fun show () =
        print (MetaPrint.sgnToString (extract ()) ^ "\n")

    fun printMenu () =
        if empty () then (show (); print "[QED]\n")
        else
          let
            val S = current ()
          in
            (print "\n";
             print (MetaPrint.stateToString S);
             print "\nSelect from the following menu:\n";
             print (menuToString ());
             print "\n")
          end


    fun contains (nil, _) = true
      | contains (x :: L, L') =
          (List.exists (fn x' => x = x') L') andalso contains (L, L')

    fun equiv (L1, L2) =
          contains (L1, L2) andalso contains (L2, L1)

    fun init' (k, cL as (c :: _)) =
        let
          val _ = MetaGlobal.maxFill := k
          val _ = reset ();
          val cL' = Order.closure c
            handle Order.Error _ => cL  (* if no termination ordering given! *)
        in
          if equiv (cL, cL') then
            map (fn S => insert S) (Init.init cL)
          else raise Error ("Theorem by simultaneous induction not correctly stated:"
                             ^ "\n            expected: " ^ (cLToString cL'))
        end

    fun init (k, nL) =
        let
          fun cids nil = nil
            | cids (name :: nL) =
              (case Names.stringToQid name
                 of NONE => raise Error ("Malformed qualified identifier " ^ name)
                  | SOME qid =>
              (case Names.constLookup qid
                 of NONE => raise Error ("Type family " ^ Names.qidToString qid ^ " not defined")
                  | SOME cid => cid :: (cids nL)))
        in
          ((init' (k, cids nL); menu (); printMenu ())
            handle Splitting.Error s => abort ("Splitting Error: " ^ s)
                 | Filling.Error s => abort ("Filling Error: " ^ s)
                 | Recursion.Error s => abort ("Recursion Error: " ^ s)
                 | Error s => abort ("Mpi Error: " ^ s))
        end

    fun select k =
        let
          fun select' (k, nil) = abort ("No such menu item")
            | select' (1, Splitting O :: _) =
                let
                  val S' = (Timers.time Timers.splitting Splitting.apply) O
                  val _ = pushHistory ()
                  val _ = delete ()
                  val _ = map insert S'
                in
                  (menu (); printMenu ())
                end
            | select' (1, Recursion O :: _) =
                let
                  val S' = (Timers.time Timers.recursion Recursion.apply) O
                  val _ = pushHistory ()
                  val _ = delete ()
                  val _ = insert S'
                in
                  (menu (); printMenu ())
                end
            | select' (1, Filling O :: _) =
                let
                  val _ =
                    case (Timers.time Timers.filling Filling.apply) O of
                      nil => abort ("Filling unsuccessful: no object found")
                    | (S :: _) => (delete ();
                                   insert S;
                                   pushHistory ())
                in
                  (menu (); printMenu ())
                end
            | select' (k, _ :: M) = select' (k-1, M)
        in
          (case !Menu of
            NONE => raise Error "No menu defined"
          | SOME M => select' (k, M))
             handle Splitting.Error s => abort ("Splitting Error: " ^ s)
                  | Filling.Error s => abort ("Filling Error: " ^ s)
                  | Recursion.Error s => abort ("Recursion Error: " ^ s)
                  | Error s => abort ("Mpi Error: " ^ s)
        end


    fun lemma name =
        if empty () then raise Error "Nothing to prove"
        else
          let
            val S = current ()
            val S' = Lemma.apply (S, valOf (Names.constLookup (valOf (Names.stringToQid name))))
              handle Splitting.Error s => abort ("Splitting Error: " ^ s)
                   | Filling.Error s => abort ("Filling Error: " ^ s)
                   | Recursion.Error s => abort ("Recursion Error: " ^ s)
                   | Error s => abort ("Mpi Error: " ^ s)
            val _ = pushHistory ()
            val _ = delete ()
            val _ = insert S'
          in
            (menu (); printMenu ())
          end

    fun solve () =
        if empty () then raise Error "Nothing to prove"
        else
          let
            val S = current ()
            val (Open', Solved') = Strategy.run [S]
              handle Splitting.Error s => abort ("Splitting Error: " ^ s)
                   | Filling.Error s => abort ("Filling Error: " ^ s)
                   | Recursion.Error s => abort ("Recursion Error: " ^ s)
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
          val (Open', Solved') = Strategy.run (collectOpen ())
            handle Splitting.Error s => abort ("Splitting Error: " ^ s)
                 | Filling.Error s => abort ("Filling Error: " ^ s)
                 | Recursion.Error s => abort ("Recursion Error: " ^ s)
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
    val lemma = lemma
    val reset = reset
    val solve = solve
    val auto = auto
    val extract = extract
    val show = show
    val undo = undo
 end (* local *)
end; (* functor MPI *)
