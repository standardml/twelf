(* Solver for a linearly ordered field, based on the simplex method *)
(* Author: Roberto Virga *)

functor CSIneqField (structure OrderedField : ORDERED_FIELD
                     (*! structure IntSyn : INTSYN !*)
                     structure Trail : TRAIL
                     structure Unify : UNIFY
                     (*! sharing Unify.IntSyn = IntSyn !*)
                     structure SparseArray  : SPARSE_ARRAY
                     structure SparseArray2 : SPARSE_ARRAY2
                     (*! structure CSManager : CS_MANAGER !*)
                     (*! sharing CSManager.IntSyn = IntSyn !*)
                     structure CSEqField : CS_EQ_FIELD
                       sharing CSEqField.Field = OrderedField
                       (*! sharing CSEqField.IntSyn = IntSyn !*)
                       (*! sharing CSEqField.CSManager = CSManager !*)
                     structure Compat : COMPAT
                         )
 : CS =
struct
  (*! structure CSManager = CSManager !*)

  local
    open IntSyn
    open OrderedField
    open CSEqField

    structure FX = CSManager.Fixity
    structure MS = ModeSyn (* CSManager.ModeSyn *)

    structure Array  = SparseArray
    structure Array2 = SparseArray2

    (* solver ID of this solver *)
    val myID = ref ~1 : cid ref

    (* constant IDs of the declared type constants *)
    val gtID   = ref ~1 : cid ref
    val geqID  = ref ~1 : cid ref

    (* constructors for the declared types *)
    fun gt (U, V) = Root (Const (!gtID), App (U, App (V, Nil)))
    fun geq (U, V) = Root (Const (!geqID), App (U, App (V, Nil)))

    (* specialized constructors for the declared types *)
    fun gt0 (U) = gt (U, constant (zero))
    fun geq0 (U) = geq (U, constant (zero))

    (* constant IDs of the declared object constants *)
    val gtAddID  = ref ~1 : cid ref
    val geqAddID = ref ~1 : cid ref
    val gtGeqID = ref ~1 : cid ref
    val geq00ID = ref ~1 : cid ref

    (* constructors for the declared objects *)
    fun gtAdd (U1, U2, V, W) =
          Root (Const (!gtAddID), App (U1, App (U2, App (V,  App (W, Nil)))))
    fun geqAdd (U1, U2, V, W) =
          Root (Const (!geqAddID), App (U1, App (U2, App (V,  App (W, Nil)))))
    fun gtGeq (U, V, W) =
          Root (Const (!gtGeqID), App (U, App (V, App (W, Nil))))
    fun geq00 () = Root (Const (!geq00ID), Nil)

    (* constant declaration for the proof object d>0 *)
    fun gtNConDec (d) = ConDec (toString (d) ^ ">" ^ toString (zero),
                                NONE, 0, Normal, gt0 (constant (d)), Type)

    (* foreign constant for the proof object d>0 *)
    fun gtNExp (d) = Root (FgnConst (!myID, gtNConDec (d)), Nil)

    (* specialized constructors for the declared objects *)
    fun geqN0 (d) =
          if (d = zero) then geq00 ()
          else gtGeq (constant (d), constant (zero), gtNExp (d))

    (* parsing proof objects d>0 *)
    fun parseGtN string =
          let
            val suffix   = (">" ^ (toString (zero)))
            val stringLen  = String.size string
            val suffixLen = String.size suffix
            val numLen  = Int.-(stringLen, suffixLen)
          in
            if Int.>(stringLen, suffixLen)
              andalso (String.substring (string, numLen, suffixLen) = suffix)
            then
              (case fromString (String.substring (string, 0, numLen))
                 of SOME(d) => if (d > zero) then SOME(gtNConDec (d))
                                else NONE
                  | NONE => NONE)
            else
              NONE
          end

    datatype Position =                               (* Position of a tableau entry       *)
      Row of int
    | Col of int

    datatype Owner =                                  (* Owner of an entry:                *)
      Var of IntSyn.dctx * Mon                        (*   - monomial                      *)
    | Exp of IntSyn.dctx * Sum                        (*   - sum                           *)

    datatype Restriction =                            (* Restriction: (proof object)       *)
      Restr of IntSyn.dctx * IntSyn.Exp * bool        (*   Restr (G, U, strict)            *)

    type label =
           {owner : Owner,                            (* owner of the row/column (if any)  *)
            tag   : int ref,                          (* tag: used to keep track of the    *)
                                                      (* position of a tableau entry       *)
            restr : Restriction option ref,           (* restriction (if any)              *)
            dead  : bool ref}                         (* has the row/column already been   *)
                                                      (* solved?                           *)

    datatype Operation =                              (* Undoable operations:              *)
      Insert of Position                              (* insert a new row/column           *)
    | Pivot of int * int                              (* pivot on (i, j)                   *)
    | Kill of Position                                (* mark the given position solved    *)
    | Restrict of Position                            (* restrict the given position       *)
    | UpdateOwner of Position * Owner * int ref       (* change the owner                  *)

    type tableau =                                    (* Tableau:                          *)
           {rlabels : label Array.array,              (* row labels                        *)
            clabels : label Array.array,              (* column labels                     *)
            consts : number Array.array,              (* constant terms                    *)
            coeffs : number Array2.array,             (* variables coefficients            *)
            nrows : int ref, ncols : int ref,         (* dimensions                        *)
            trail : Operation Trail.trail}            (* undo mechanism                    *)

    exception MyFgnCnstrRep of int ref                (* FgnCnstr representation *)

    exception Error

    (* Representational invariants:
         rlabels[i] = vacuous
         clabels[j] = vacuous
         const[i] = zero
         coeff[i,j] = zero
       for i >= !nrows or j > !ncols, where "vacuous" is the vacuous label:
          #owner(vacuous) = Exp (Null, Sum (zero, nil))
          #restr(vacuous) = ref NONE
          #dead(vacuous) = ref true
    *)

    (* little random generation routine taken from Paulson '91 *)
    local
      val a = 16807.0 and m = 2147483647.0
      val seed = ref 1999.0
    in
      fun rand (min, size) =
        let
          fun nextrand ()=
                let
                  val t = Real.*(a, !seed)
                in
                  (
                    seed := Real.-(t, Real.*(m, Real.fromInt(Real.floor(t/m))));
                    Real.-(!seed, 1.0) / Real.-(m, 1.0)
                  )
                end
        in
          Int.+(min, Real.floor(Real.*(nextrand(), Real.fromInt(size))))
        end
    end

    (* create a new (empty) tableau *)
    val tableau =
          let
            val l = {owner = Exp (Null, Sum (zero, nil)), tag = ref 0,
                     restr = ref NONE, dead = ref true}
          in
            {rlabels = Array.array (l), clabels = Array.array (l),
             consts = Array.array (zero), coeffs = Array2.array (zero),
             nrows = ref 0, ncols = ref 0, trail = Trail.trail ()} : tableau
          end

    (* i-th tableau row label *)
    fun rlabel (i) =
          Array.sub (#rlabels(tableau), i)

    (* j-th tableau column label *)
    fun clabel (j) =
          Array.sub (#clabels(tableau), j)

    (* i-th tableau constant term *)
    fun const (i) =
          Array.sub (#consts(tableau), i)

    (* coefficient in row i, column j *)
    fun coeff (i, j) =
          Array2.sub (#coeffs(tableau), i, j)

    (* number of rows *)
    fun nRows () = !(#nrows(tableau))

    (* number of columns *)
    fun nCols () = !(#ncols(tableau))

    (* increase the number of rows, and return the index of the last row *)
    fun incrNRows () =
          let
            val old = nRows ()
          in
            (#nrows(tableau) := Int.+(old, 1); old)
          end

    (* increase the number of columns, and return the index of the last column *)
    fun incrNCols () =
          let
            val old = nCols ()
          in
            (#ncols(tableau) := Int.+(old, 1); old)
          end

    (* decrease the number of rows *)
    fun decrNRows () =
          #nrows(tableau) := Int.-(nRows(), 1)

    (* decrease the number of columns *)
    fun decrNCols () =
          #ncols(tableau) := Int.-(nCols(), 1)

    (* increase by the given amount the element i of the array *)
    fun incrArray (array, i, value) =
          Array.update (array, i, Array.sub (array, i) + value)

    (* increase by the given amount the element (i, j) of the array *)
    fun incrArray2 (array, i, j, value) =
          Array2.update (array, i, j, Array2.sub (array, i, j) + value)

    (* increase by f(j') all the elements (i, j'), with j <= j' < j+len *)
    fun incrArray2Row (array, i, (j, len), f) =
          Compat.Vector.mapi
            (fn (j, value) => Array2.update (array, i, j, value + f(j)))
            (Array2.row (array, i, (j, len)))

    (* increase by f(i') all the elements (i', j), with i <= i' < i+len *)
    fun incrArray2Col (array, j, (i, len), f) =
          Compat.Vector.mapi
            (fn (i, value) => Array2.update (array, i, j, value + f(i)))
            (Array2.column (array, j, (i, len)))

    (* set the given row to zero *)
    fun clearArray2Row (array, i, (j, len)) =
          Compat.Vector.mapi
            (fn (j, value) => Array2.update (array, i, j, zero))
            (Array2.row (array, i, (j, len)))

    (* set the given column to zero *)
    fun clearArray2Col (array, j, (i, len)) =
          Compat.Vector.mapi
            (fn (i, value) => Array2.update (array, i, j, zero))
            (Array2.column (array, j, (i, len)))

    (* return the label at the given position (row or column) *)
    fun label (Row(i)) = rlabel (i)
      | label (Col(j)) = clabel (j)

    (* return the restriction on the given label *)
    fun restriction (l : label) = !(#restr(l))

    (* is the given label is restricted? *)
    fun restricted (l : label) =
          (case (restriction (l))
             of SOME _ => true
              | NONE => false)

    (* return true iff the given label has been solved *)
    fun dead (l : label) = !(#dead(l))

    (* set the ownership of the given position *)
    fun setOwnership (pos, owner, tag) =
          let
            val old = label(pos)
            val new = {owner = owner,
                       tag = tag,
                       restr = ref (restriction (old)),
                       dead = ref (dead (old))}
          in
            (case pos
               of Row(i) =>
                    Array.update (#rlabels(tableau), i, new)
                | Col(j) =>
                    Array.update (#clabels(tableau), j, new))
          end

    (* return the context of a owner *)
    fun ownerContext (Var (G, mon)) = G
      | ownerContext (Exp (G, sum)) = G

    (* return the owner as a sum *)
    fun ownerSum (Var (G, mon)) = Sum(zero, [mon])
      | ownerSum (Exp (G, sum)) = sum

    (* debugging code - REMOVE *)
    fun displayPos (Row(row)) =
          print ("row " ^ Int.toString(row) ^ "\n")
      | displayPos (Col(col)) =
          print ("column " ^ Int.toString(col) ^ "\n")

    (* debugging code - REMOVE *)
    fun displaySum (Sum(m, Mon(n, _) :: monL)) =
          (
            print (OrderedField.toString n);
            print " ? + ";
            displaySum (Sum(m, monL))
          )
      | displaySum (Sum(m, nil)) =
          (
            print (OrderedField.toString m);
            print " >= 0\n"
          )

    (* debugging code - REMOVE *)
    fun display () =
          let
            fun printLabel (col, l : label) =
                  (
                    print "\t";
                    (case (#owner(l)) of Var _ => print "V" | Exp _ => print "E");
                    if restricted (l) then print ">" else print "*";
                    if dead (l) then print "#" else print ""
                  )
            fun printRow (row, l : label) =
                  let
                    fun printCol (col, d : number) =
                          (
                            print "\t";
                            print (toString d)
                          )
                    val vec = Array2.row (#coeffs(tableau), row, (0, nCols()))
                  in
                    (
                      (case (#owner(l)) of Var _ => print "V" | Exp _ => print "E");
                      if restricted (l) then print ">" else print "*";
                      if dead (l) then print "#" else print "";
                      print "\t";
                      Compat.Vector.mapi printCol vec;
                      print "\t";
                      print (toString (const (row)));
                      print "\n"
                    )
                  end
          in
            (
              print "\t";
              Array.app printLabel (#clabels(tableau), 0, nCols());
              print "\n";
              Array.app printRow (#rlabels(tableau), 0, nRows());
              print "Columns:\n";
              Array.app (fn (_, l : label) => displaySum (ownerSum (#owner (l))))
                        (#clabels(tableau), 0, nCols());
              print "Rows:\n";
              Array.app (fn (_, l : label) => displaySum (ownerSum (#owner (l))))
                        (#rlabels(tableau), 0, nRows())
            )
          end

    (* find the given monomial in the tableau *)
    fun findMon (mon) =
          let
            exception Found of int

            fun find (i, l : label) =
                  (case (#owner(l))
                     of (Var (G, mon')) =>
                          if compatibleMon (mon, mon')
                          then raise Found i
                          else ()
                      | _ => ())
          in
            (Array.app find (#clabels(tableau), 0, nCols());
               (Array.app find (#rlabels(tableau), 0, nRows());
                  NONE)
                handle Found i => SOME(Row(i)))
             handle Found j => SOME(Col(j))
          end

    (* return the a position in the tableau of the tagged expression *)
    fun findTag (t) =
          let
            exception Found of int

            fun find (i, l : label) =
                  if (#tag(l) = t)
                  then raise Found i
                  else ()
          in
            (Array.app find (#clabels(tableau), 0, nCols());
               (Array.app find (#rlabels(tableau), 0, nRows());
                  NONE)
                handle Found i => SOME(Row(i)))
             handle Found j => SOME(Col(j))
          end

    (* return true iff the given row is null at all the active columns *)
    fun isConstant (row) =
          Array.foldl
           (fn (j, l, rest) =>
              (dead (l) orelse (coeff (row, j) = zero)) andalso rest)
           true
           (#clabels(tableau), 0, nCols())

    (* return the position of the row/column of the tableau (if any) that makes the
       given row redundant *)
    fun isSubsumed (row) =
          let
            val constRow = const (row)

            fun isSubsumedByRow () =
                  let
                    (* the candidates are those (active) rows with the same constant
                       term *)
                    val candidates =
                          Array.foldl
                            (fn (i, l : label, rest) =>
                               if (i <> row)
                                 andalso not (dead (l))
                                 andalso (const (i) = constRow)
                               then (i :: rest)
                               else rest)
                            nil
                            (#rlabels(tableau), 0, nRows())
                    (* if j is active, trim the list of candidates to those that have
                       the same coefficient in column j
                    *)
                    fun filter (j, l, nil) = nil
                      | filter (j, l : label, candidates) =
                          if not (dead (l))
                          then
                             List.filter
                               (fn i => (coeff (i, j) = coeff (row, j)))
                               candidates
                          else
                            candidates
                  in
                    (case (Array.foldl filter candidates
                                       (#clabels(tableau), 0, nCols()))
                       of nil => NONE
                        | (i :: _) => SOME(i))
                  end

            fun isSubsumedByCol () =
                  if (constRow = zero)
                  then
                    let
                      (* compute the list of non-null coefficients in the row *)
                      val nonNull =
                            Array.foldl
                              (fn (j, l : label, rest) =>
                                 if not (dead (l))
                                 then
                                   let
                                     val value = coeff (row, j)
                                   in
                                     if (value <> zero)
                                     then ((j, value) :: rest)
                                     else rest
                                   end
                                 else
                                   rest)
                             nil
                             (#clabels(tableau), 0, nCols())
                    in
                      (case nonNull
                         of [(j, value)] =>
                              if (value = one) then SOME(j)
                              else NONE
                          | _ => NONE)
                    end
                  else
                    NONE
          in
            case isSubsumedByRow ()
              of SOME(i) => SOME(Row(i))
               | NONE => (case isSubsumedByCol ()
                            of SOME(j) => SOME(Col(j))
                             | NONE => NONE)
          end

     (* find the coordinates of the pivot which gives the largest increase in const(row) *)
     fun findPivot (row) =
          let
            (* extend Field.compare to deal with NONE (= infinity) *)
            fun compareScore (SOME(d), SOME(d')) =
                  compare (d, d')
              | compareScore (SOME(d), NONE) = LESS
              | compareScore (NONE, SOME(d')) = GREATER
              | compareScore (NONE, NONE) = EQUAL

            (* find the best pivot candidates for the given row *)
            fun findPivotCol (j, l : label, result as (score, champs)) =
                  let
                    val value = coeff(row, j)
                    (* find the best pivot candidates for the given row and column *)
                    fun findPivotRow sgn (i, l : label, result as (score, champs)) =
                          let
                            val value = coeff (i, j)
                          in
                            if (not (dead (l))) andalso (i <> row) andalso restricted (l)
                              andalso ((fromInt (sgn) * value) < zero)
                            then
                              let
                                val score' = SOME(abs (const (i) * inverse (value)))
                              in
                                case compareScore (score, score')
                                  (* always choose the smallest *)
                                  of GREATER => (score', [(i, j)])
                                   | EQUAL => (score, (i, j) :: champs)
                                   | LESS => result
                              end
                            else
                              result
                          end
                  in
                    if (not (dead (l))) andalso (value <> zero)
                      andalso (not (restricted (l)) orelse (value > zero))
                    then
                      let
                        val (result' as (score', champs')) =
                              Array.foldl (findPivotRow (sign value))
                                                (NONE, [(row, j)])
                                                (#rlabels(tableau), 0, nRows ())
                      in
                        case compareScore (score, score')
                          (* always choose the largest *)
                          of GREATER => result
                           | EQUAL => (score, champs @ champs')
                           | LESS => result'
                      end
                    else
                      result
                  end
          in
            case (Array.foldl findPivotCol (SOME(zero), nil)
                                    (#clabels(tableau), 0, nCols ()))
              of (_, nil) => NONE
               | (_, champs) =>
                   (* choose one randomly to ensure fairness *)
                   SOME(List.nth (champs, rand (0, List.length (champs))))
          end

    (* pivot the element at the given coordinates *)
    fun pivot (row, col) =
          let
            val pCoeffInverse = inverse (coeff (row, col))

            val pRowVector =
                  Array2.row (#coeffs(tableau), row, (0, nCols ()))
            fun pRow(j) = Vector.sub (pRowVector, j)

            val pColVector =
                  Array2.column (#coeffs(tableau), col, (0, nRows ()))
            fun pCol(i) = Vector.sub (pColVector, i)

            val pConst = const (row)

            val pRLabel = rlabel (row)
            val pCLabel = clabel (col)
          in
            (
               Array.modify
                 (fn (i, value) =>
                    if (i = row) then
                      (* same row as the pivot *)
                      ~(value * pCoeffInverse)
                    else
                      (* any other row *)
                      value - (pConst * pCol(i) * pCoeffInverse))
                 (#consts(tableau), 0, nRows());

                Array2.modify Array2.ColMajor
                  (fn (i, j, value) =>
                     (case (i = row, j = col)
                        of (true, true) =>
                             (* pivot *)
                             pCoeffInverse
                         | (true, false) =>
                             (* same row as the pivot *)
                             ~(value * pCoeffInverse)
                         | (false, true) =>
                             (* same column as the pivot *)
                             value * pCoeffInverse
                         | (false, false) =>
                             (* any other row/column *)
                             value - (pRow(j) * pCol (i) * pCoeffInverse)))
                  {base = (#coeffs(tableau)), row = 0, col = 0,
                   nrows = nRows(), ncols = nCols ()};

               Array.update (#rlabels(tableau), row, pCLabel);
               Array.update (#clabels(tableau), col, pRLabel)
            )
          end

    datatype MaximizeResult =              (* Result of maximization of a row:             *)
      Positive                             (* manifestly maximized at some value > 0       *)
    | Maximized of number                  (* manifestly maximized at c <= 0               *)
    | Unbounded of int                     (* manifestly unbounded, pivoting on column col *)

    (* maximize the given row by performing pivot operations.
       Return a term of type MaximizeResult.
    *)
    fun maximizeRow (row) =
          let
            val value = const(row)
          in
            if (value <= zero)
            then
              case findPivot (row)
                of SOME(i,j) =>
                     if (i <> row) then
                       (
                         Trail.log (#trail(tableau), Pivot(i, j));
                         pivot (i, j);
                         maximizeRow row
                       )
                     else
                       Unbounded j
                 | NONE =>
                     Maximized value
            else
              Positive
          end

    (* delay all terms of a monomial on the given constraint *)
    fun delayMon (Mon(n, UsL), cnstr) =
          List.app (fn Us => Unify.delay (Us, cnstr)) UsL

    (* unify two restrictions *)
    fun unifyRestr (Restr (G, proof, strict), proof') =
          if Unify.unifiable (G, (proof, id), (proof', id)) then ()
          else raise Error

    (* unify a sum with a number *)
    fun unifySum (G, sum, d) =
          if Unify.unifiable (G, (toExp (sum), id), (constant (d), id)) then ()
          else raise Error

    (* decomposition of an expression as the weighted sum of tableau positions *)
    type decomp = number * (number * Position) list

    (* change sign to the given decomposition *)
    fun unaryMinusDecomp ((d, wposL)) =
          (~d, List.map (fn (d, pos) => (~d, pos)) wposL)

    (* decompose a sum in whnf into a weighted sum of tableau positions *)
    fun decomposeSum (G, Sum (m, monL)) =
          let
            fun monToWPos (mon as (Mon (n, UsL))) =
                  (case findMon (mon)
                     of SOME(pos) => (n, pos)
                      | NONE =>
                          let
                            val new = incrNCols()
                            val l = {owner = Var (G, Mon (one, UsL)),
                                     tag = ref 0,
                                     restr = ref NONE,
                                     dead = ref false}
                          in
                             (
                               Trail.log (#trail(tableau), Insert(Col(new)));
                               delayMon (mon, ref (makeCnstr (#tag(l))));
                               Array.update (#clabels(tableau), new, l);
                               (n, Col(new))
                             )
                          end)
          in
            (m, List.map monToWPos monL)
          end

    (* insert the given expression in the tableau, labelling it with owner *)
    and insertDecomp (decomp as (d, wposL), owner) =
          let
            val new = incrNRows ()

            fun insertWPos (d, pos) =
                  (case pos
                     of Row(row) =>
                          (
                            incrArray2Row (#coeffs(tableau), new,
                                           (0, nCols()),
                                           (fn (j) =>
                                              d*coeff(row, j)));
                            incrArray (#consts(tableau), new,
                                       d*const(row))
                          )
                      | Col(col) =>
                          incrArray2 (#coeffs(tableau), new, col, d))
          in
            (
              (* add the decomposition to the newly created row *)
              List.app insertWPos wposL;
              incrArray(#consts(tableau), new, d);
              (* is this row trivial? *)
              case isSubsumed (new)
                of SOME(pos) =>
                     (
                       clearArray2Row (#coeffs(tableau), new, (0, nCols()));
                       Array.update (#consts(tableau), new, zero);
                       decrNRows ();
                       pos
                     )
                 | NONE =>
                     (
                       setOwnership (Row(new), owner, ref 0);
                       #dead(label(Row(new))) := isConstant(new);
                       (* log the creation of this row *)
                       Trail.log (#trail(tableau), Insert(Row(new)));
                       (* return its position *)
                       Row(new)
                     )
            )
          end

    (* insert the given (unrestricted) expression in the tableau *)
    and insert (G, Us) =
          let
            val sum = fromExp Us
          in
            insertDecomp (decomposeSum (G, sum), Exp (G, sum))
          end

    (* minimize a tableau that has been determined non-minimal (but consistent) as a
       consequence of adding the given row.
    *)
    and minimize (row) =
          let
            (* equate the given column to zero if coeff(row, j) <> zero *)
            fun killColumn (j, l : label) =
                  if (not (dead(l)))
                    andalso (coeff(row, j) <> zero)
                  then
                    (
                      (* mark the column dead *)
                      Trail.log (#trail(tableau), Kill(Col(j)));
                      #dead(Array.sub (#clabels(tableau), j)) := true;
                      (* if restricted, instantiate the proof object to 0>=0 *)
                      (case restriction (l)
                         of SOME(restr) =>
                              unifyRestr (restr, geq00 ())
                          | NONE => ());
                      (* if owned by a monomial, unify it with zero *)
                      (case #owner(l)
                         of (owner as (Var _)) =>
                              unifySum (ownerContext (owner), ownerSum (owner), zero)
                          | _ => ())
                    )
                  else ()
            (* find out if the given row has been made trivial by killing some
               columns
            *)
            fun killRow (i, l : label) =
                  if not (dead(l))
                  then
                    if isConstant (i)
                    then (* row is now constant and equal to n = const(i) *)
                      (
                        (* mark the row dead *)
                        Trail.log (#trail(tableau), Kill(Row(i)));
                        #dead(Array.sub (#rlabels(tableau), i)) := true;
                        (* if restricted, instantiate the proof object to n>=0 *)
                        (case restriction (l)
                           of SOME(restr) =>
                                unifyRestr (restr, geqN0 (const(i)))
                            | NONE => ());
                        (* if owned by a monomial, unify it with n *)
                        (case #owner(l)
                           of (owner as (Var _)) =>
                                unifySum (ownerContext (owner), ownerSum (owner), const(i))
                            | _ => ())
                      )
                    else
                      case isSubsumed (i)
                        of SOME(pos') =>
                             let
                               val l' = label(pos')
                             in
                               (
                                 Trail.log (#trail(tableau), Kill(Row(i)));
                                 #dead(Array.sub (#rlabels(tableau), i)) := true;
                                 (case (restriction (l), restriction (l'))
                                    of (SOME(restr), SOME(Restr(_, proof', _))) =>
                                         unifyRestr (restr, proof')
                                     | (SOME _, NONE) =>
                                         (
                                           (* it is safe to restrict without doing all
                                              the checks in this case, since the two rows
                                              are identical *)
                                           Trail.log (#trail(tableau), Restrict(pos'));
                                           #restr(l') := restriction (l)
                                         )
                                     | (NONE, _) => ())
                               )
                             end
                         | NONE => ()
                  else ()
          in
            (
              Array.app killColumn (#clabels(tableau), 0, nCols());
              Array.app killRow (#rlabels(tableau), 0, nRows())
            )
          end

    (* restrict the given row/column to be nonnegative *)
    and restrict (pos as Col(col), restr) =
          let
            val l = label(pos)
          in
            if dead(l)
            then
              unifyRestr (restr, geq00 ())
            else
              case restriction (l)
                of SOME(Restr(_, proof', _)) =>
                     unifyRestr (restr, proof')
                 | NONE =>
                     let
                       (* compute the list of non-null row entries *)
                       val nonNull =
                             Array.foldl
                               (fn (i, l : label, rest) =>
                                  if not (dead(l))
                                  then
                                    let
                                      val value = coeff (i, col)
                                    in
                                      if (value <> zero) then (i :: rest)
                                      else rest
                                    end
                                  else
                                    rest)
                             nil
                             (#rlabels(tableau), 0, nRows())
                     in
                       case nonNull
                         of (row :: _) =>
                              (
                                (* pivot to a row position; this is sound since
                                   the column is unrestricted (see Nelson '81)
                                *)
                                Trail.log (#trail(tableau), Pivot(row, col));
                                pivot (row, col);
                                restrict (Row(row), restr)
                              )
                          | nil =>
                              (
                                (* the column is zero at all the active row
                                   positions, so we can restrict it right away
                                *)
                                Trail.log (#trail(tableau), Restrict(Col(col)));
                                #restr(label(Col(col))) := SOME(restr)
                              )
                     end
          end
      | restrict (pos as Row(row), restr) =
          let
            val l = label(pos)
          in
            if dead(l)
            then
              unifyRestr (restr, geqN0 (const(row)))
            else
              case restriction (l)
                of SOME(Restr(_, proof', _)) =>
                     unifyRestr (restr, proof')
                | NONE =>
                     case maximizeRow row
                       of Unbounded col =>
                            (
                              Trail.log (#trail(tableau), Restrict(Row(row)));
                              #restr(Array.sub (#rlabels(tableau), row)) := SOME(restr);
                              if (const(row) < zero)
                              then
                                (
                                  Trail.log (#trail(tableau), Pivot(row, col));
                                  pivot (row, col)
                                )
                              else ()
                            )
                        | Positive =>
                              (
                                (* the tableau is satisfiable and minimal *)
                                Trail.log (#trail(tableau), Restrict(Row(row)));
                                #restr(Array.sub (#rlabels(tableau), row)) := SOME(restr)
                              )
                        | Maximized value =>
                            if (value = zero)
                            then
                              (
                                (* the tableau is satisfiable but not minimal*)
                                Trail.log (#trail(tableau), Restrict(Row(row)));
                                #restr(Array.sub (#rlabels(tableau), row)) := SOME(restr);
                                minimize (row)
                              )
                            else raise Error
          end

    (* insert the equality Var(pos) = Us as two inequalities:
         Var(pos) - Us >= zero
         Us - Var(pos) >= zero
    *)
    and insertEqual (G, pos, sum) =
          let
            val (m, wposL) = decomposeSum (G, sum)

            val decomp' = (m, (~one, pos) :: wposL)
            val pos' = insertDecomp (decomp', Exp (G, Sum(zero, nil)))

            val decomp'' = unaryMinusDecomp (decomp')
            val tag'' = #tag(label (insertDecomp (decomp'', Exp (G, Sum(zero, nil)))))
          in
            (
               (* the second expression may change position when we
                  restrict the first. We use tags to keep track of it *)
               restrict (pos', Restr (G, geq00 (), false));
               (case findTag (tag'')
                  of SOME(pos'') =>
                       restrict (pos'', Restr (G, geq00 (), false)))
            )
          end

    (* update the tableau upon discovery that Var(pos) = sum *)
    and update (G, pos, sum) =
          let
            val l = label (pos)
          in
            (
              (* if the given position has a owner, delete it, since not doing so
                 may violate the invariant *)
              Trail.log (#trail(tableau), UpdateOwner(pos, #owner(l), #tag(l)));
              setOwnership (pos, Exp (G, sum), ref 0);
              (* analyze the given position to see exactly how to represent this
                 equality *)
              if dead(l)
              then
                (case pos
                   of Row(row) =>
                        (* find out why it died *)
                        if isConstant (row)
                        then
                          (* row is dead because constant and equal to n *)
                          unifySum (G, sum, const(row))
                        else
                          (* row is dead because is subsumed by another *)
                          (case isSubsumed (row)
                             of SOME(pos') => update (G, pos', sum))
                    | Col(col) =>
                        (* column is dead because = 0 *)
                        unifySum (G, sum, zero))
              else
                let
                  fun isVar (Sum(m, [mon as Mon(n, _)])) =
                        if (m = zero) andalso (n = one)
                        then SOME(mon)
                        else NONE
                    | isVar (sum) = NONE
                in
                  case isVar (sum)
                    of SOME(mon) =>
                         (* the nf is another variable *)
                         (case findMon (mon)
                            of SOME _ => insertEqual (G, pos, sum)
                             | NONE =>
                                let
                                  val tag = ref 0
                                in
                                  (
                                    (* recycle the current label *)
                                    Trail.log (#trail(tableau),
                                               UpdateOwner (pos, #owner(l), #tag(l)));
                                    setOwnership (pos, Var (G, mon), tag);
                                    delayMon (mon, ref (makeCnstr (tag)))
                                  )
                                end)
                     | NONE => insertEqual (G, pos, sum)
                 end
            )
          end

    (* returns the list of unsolved constraints associated with the given position *)
    and restrictions (pos) =
          let
            fun member (x, l) = List.exists (fn y => x = y) l
            fun test (l) = restricted(l) andalso not (dead(l))
            fun reachable ((pos as Row(row)) :: candidates, tried, closure) =
                  if member (pos, tried)
                  then reachable (candidates, tried, closure)
                  else
                    let
                      val new_candidates =
                            Array.foldl
                              (fn (col, _, candidates) =>
                                    if (coeff(row, col) <> zero)
                                    then (Col(col)) :: candidates
                                    else candidates)
                              nil
                              (#clabels(tableau), 0, nCols())
                      val closure' = if test (label(pos)) then (pos :: closure)
                                     else closure
                    in
                      reachable (new_candidates @ candidates,
                                 pos :: tried,
                                 closure')
                    end
              | reachable ((pos as Col(col)) :: candidates, tried, closure) =
                  if member (pos, tried)
                  then reachable (candidates, tried, closure)
                  else
                    let
                      val candidates' =
                            Array.foldl
                              (fn (row, _, candidates) =>
                                    if (coeff(row, col) <> zero)
                                    then (Row(row)) :: candidates
                                    else candidates)
                              nil
                              (#rlabels(tableau), 0, nRows())
                      val closure' = if test (label(pos)) then (pos :: closure)
                                     else closure
                    in
                      reachable (candidates' @ candidates,
                                 pos :: tried,
                                 closure')
                    end
              | reachable (nil, _, closure) = closure
            fun restrExp (pos) =
                  let
                    val l = label(pos)
                    val owner = #owner(l)
                    val G = ownerContext (owner)
                    val U = toExp (ownerSum (owner))
                  in
                    (case restriction (label(pos))
                       of SOME(Restr(_, _, true)) => (G, gt0 (U))
                        | _ => (G, geq0 (U)))
                  end

          in
            List.map restrExp (reachable ([pos], nil, nil))
          end

    (* create a foreingn constraint for the given tag *)
    and makeCnstr (tag) =
          FgnCnstr (!myID, MyFgnCnstrRep tag)

    (* returns the list of unsolved constraints associated with the given tag *)
    fun toInternal (tag) () =
           (case findTag (tag)
              of NONE => nil
               | SOME(pos) => restrictions (pos))

    (* awake function for tableau constraints *)
    fun awake (tag) () =
          (
            (case findTag (tag)
               of SOME(pos) =>
                    let
                      val owner = #owner(label (pos))
                      val G = ownerContext(owner)
                      val sum = normalize (ownerSum (owner))
                    in
                      (update (G, pos, sum) ; true)
                    end
                | NONE => true)
            handle Error => false
          )

    (* simplify function for tableau constraints *)
    fun simplify (tag) () =
          (case toInternal (tag) ()
             of nil => true
              | (_ :: _) => false)

    (* undo function for trailing tableau operations *)
    fun undo (Insert(Row(row))) =
          (
            #dead(Array.sub (#rlabels(tableau), row)) := true;
            clearArray2Row (#coeffs(tableau), row, (0, nCols()));
            Array.update(#consts(tableau), row, zero);
            decrNRows ()
          )
      | undo (Insert(Col(col))) =
          (
            #dead(Array.sub (#clabels(tableau), col)) := true;
            clearArray2Col (#coeffs(tableau), col, (0, nRows()));
            decrNCols ()
          )
      | undo (Pivot(row, col)) =
          pivot(row, col)
      | undo (Kill(pos)) =
          #dead(label(pos)) := false
      | undo (Restrict(pos)) =
          #restr(label(pos)) := NONE
      | undo (UpdateOwner(pos, owner, tag)) =
          setOwnership (pos, owner, tag)

    (* reset the internal status of the tableau *)
    fun reset () =
          let
            val l = {owner = Exp (Null, Sum(zero, nil)), tag = ref 0,
                     restr = ref NONE, dead = ref true}
          in
            (
               Array.modify
                 (fn _ => l)
                 (#rlabels(tableau), 0, nRows());
               Array.modify
                 (fn _ => l)
                 (#clabels(tableau), 0, nCols());
               Array.modify
                 (fn _ => zero)
                 (#consts(tableau), 0, nRows());
               Array2.modify
                 Array2.RowMajor (fn _ => zero)
                 {base = #coeffs(tableau), row = 0, col = 0,
                  nrows = nRows(), ncols = nCols()};
               #nrows(tableau) := 0; #ncols(tableau) := 0;
               Trail.reset (#trail(tableau))
            )
          end

    (* trailing functions *)
    fun mark () =
          Trail.mark (#trail(tableau))

    fun unwind () =
          Trail.unwind (#trail(tableau), undo)

    (* fst (S, s) = U1, the first argument in S[s] *)
    fun fst (App (U1, _), s) = (U1, s)
      | fst (SClo (S, s'), s) = fst (S, comp (s', s))

    (* snd (S, s) = U2, the second argument in S[s] *)
    fun snd (App (U1, S), s) = fst (S, s)
      | snd (SClo (S, s'), s) = snd (S, comp (s', s))

    (* checks if the given foreign term can be simplified to a constant *)
    fun isConstantExp (U) =
          (case (fromExp (U, id))
             of (Sum (m, nil)) => SOME(m)
              | _ => NONE)

    (* checks if the given foreign term can be simplified to zero *)
    fun isZeroExp (U) =
          (case isConstantExp (U)
             of SOME(d) => (d = zero)
              | NONE => false)

    (* solveGt (G, S, n) tries to find the n-th solution to G |- '>' @ S : type *)
    fun solveGt (G, S, 0) =
          let
            fun solveGt0 (W) =
                  (case isConstantExp (W)
                     of SOME(d) =>
                          if (d > zero) then gtNExp (d) else raise Error
                      | NONE =>
                          let
                            val proof = newEVar (G, gt0 (W))
                            val _ = restrict (insert (G, (W, id)),
                                              Restr (G, gtGeq (W, constant (zero), proof), true));
                          in
                            proof
                          end)

            val U1 = EClo (fst (S, id))
            val U2 = EClo (snd (S, id))
          in
            (
              if isZeroExp (U2)
              then SOME(solveGt0 (U1))
              else
                let
                  val W = minus (U1, U2)
                  val proof = solveGt0 (W)
                in
                  SOME(gtAdd (W, constant (zero), U2, proof))
                end
            ) handle Error => NONE
          end
      | solveGt (G, S, n) = NONE

    (* solveGeq (G, S, n) tries to find the n-th solution to G |- '>=' @ S : type *)
    fun solveGeq (G, S, 0) =
          let
            fun solveGeq0 (W) =
                  (case isConstantExp (W)
                     of SOME(d) =>
                          if (d >= zero) then geqN0 (d) else raise Error
                      | NONE =>
                          let
                            val proof = newEVar (G, geq0 (W))
                            val _ = restrict (insert (G, (W, id)),
                                       Restr (G, proof, false))
                          in
                            proof
                          end)

            val U1 = EClo (fst (S, id))
            val U2 = EClo (snd (S, id))
          in
            (
              if isZeroExp (U2)
              then SOME(solveGeq0 (U1))
              else
                let
                  val W = minus (U1, U2)
                  val proof = solveGeq0 (W)
                in
                  SOME(geqAdd (W, constant (zero), U2, proof))
                end
            ) handle Error => NONE
          end
      | solveGeq (G, S, n) = NONE

    (* constructors for higher-order types *)
    fun pi (name, U, V) = Pi ((Dec (SOME(name), U), Maybe), V)
    fun arrow (U, V) = Pi ((Dec (NONE, U), No), V)

    fun installFgnCnstrOps () = let
        val csid = !myID
        val _ = FgnCnstrStd.ToInternal.install (csid,
                                                (fn (MyFgnCnstrRep tag) => toInternal (tag)
                                                  | fc => raise UnexpectedFgnCnstr fc))
        val _ = FgnCnstrStd.Awake.install (csid,
                                           (fn (MyFgnCnstrRep tag) => awake (tag)
                                             | fc => raise UnexpectedFgnCnstr fc))
        val _ = FgnCnstrStd.Simplify.install (csid,
                                              (fn (MyFgnCnstrRep tag) => simplify (tag)
                                                | fc => raise UnexpectedFgnCnstr fc))
    in
        ()
    end

    (* install the signature *)
    fun init (cs, installF) =
          (
            myID := cs;

            gtID :=
              installF (ConDec (">", NONE, 0,
                                Constraint (!myID, solveGt),
                                arrow (number (),
                                       arrow (number (), Uni (Type))), Kind),
                        SOME(FX.Infix(FX.minPrec, FX.None)),
                        [MS.Mapp(MS.Marg(MS.Star, NONE),
                                MS.Mapp(MS.Marg(MS.Star, NONE), MS.Mnil))]);

            geqID :=
              installF (ConDec (">=", NONE, 0,
                                Constraint (!myID, solveGeq),
                                arrow (number (), arrow (number (), Uni (Type))), Kind),
                        SOME(FX.Infix(FX.minPrec, FX.None)),
                        [MS.Mapp(MS.Marg(MS.Star, NONE),
                                MS.Mapp(MS.Marg(MS.Star, NONE), MS.Mnil))]);

            gtAddID :=
              installF (ConDec ("+>", NONE, 2, Normal,
                                pi ("X", number(),
                                    pi ("Y", number(),
                                        pi ("Z", number(),
                                            arrow (gt (Root (BVar 3, Nil),
                                                       Root (BVar 2, Nil)),
                                                   gt (plus (Root (BVar 4, Nil),
                                                             Root (BVar 2, Nil)),
                                                       plus (Root (BVar 3, Nil),
                                                             Root (BVar 2, Nil))))))),
                                Type),
                        NONE, nil);

            geqAddID :=
              installF (ConDec ("+>=", NONE, 2, Normal,
                                pi ("X", number(),
                                    pi ("Y", number(),
                                        pi ("Z", number(),
                                            arrow (geq (Root (BVar 3, Nil),
                                                        Root (BVar 2, Nil)),
                                                   geq (plus (Root (BVar 4, Nil),
                                                              Root (BVar 2, Nil)),
                                                        plus (Root (BVar 3, Nil),
                                                              Root (BVar 2, Nil))))))),
                                Type),
                        NONE, nil);

            gtGeqID :=
              installF (ConDec (">>=", NONE, 2, Normal,
                                pi ("X", number(),
                                    pi ("Y", number(),
                                        arrow (gt (Root (BVar 2, Nil),
                                                   Root (BVar 1, Nil)),
                                               geq (Root (BVar 3, Nil),
                                                    Root (BVar 2, Nil))))),
                                Type),
                        NONE, nil);

            geq00ID :=
              installF (ConDec ("0>=0", NONE, 0, Normal,
                                geq0 (constant (zero)),
                                Type),
                        NONE, nil);

            installFgnCnstrOps ();
            ()
          )
  in
    val solver =
          {
            name = ("inequality/" ^ OrderedField.name ^ "s"),
            keywords = "arithmetic,inequality",
            needs = ["Unify", #name(CSEqField.solver)],

            fgnConst = SOME({parse = parseGtN}),

            init = init,

            reset  = reset,
            mark   = mark,
            unwind = unwind
          } : CSManager.solver
  end
end  (* functor CSIneqField *)
