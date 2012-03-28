(* Sparse 1-Dimensional Arrays *)
(* Author: Roberto Virga *)

functor SparseArray (structure IntTable : TABLE where type key = int)
  :> SPARSE_ARRAY =
struct

  type 'a array = {default : 'a, table : 'a IntTable.Table}

  val size = 29;

  fun unsafeSub ({table, default}, i) =
        case (IntTable.lookup table i)
          of NONE => default
           | SOME(v) => v

  fun unsafeUpdate ({table, default}, i, v) =
        IntTable.insert table (i, v)

  fun array default =
        {default = default, table = IntTable.new size}

  fun sub (array, i) =
        if (i >= 0)
        then unsafeSub (array, i)
        else raise General.Subscript

  fun update (array, i, v) =
        if (i >= 0)
        then unsafeUpdate (array, i, v)
        else raise General.Subscript

  fun extract (array, i, len) =
        if (i >= 0) andalso (len >= 0)
        then Vector.tabulate (len, (fn off => unsafeSub (array, i+off)))
        else raise General.Subscript

  fun copyVec {src, si, len, dst, di} =
        if (di >= 0)
        then
          VectorSlice.appi (fn (i, v) => unsafeUpdate (dst, i, v))
                           (VectorSlice.slice (src, si, len))
        else raise General.Subscript

  fun app f (array, i, len) =
        if (i >= 0) andalso (len >= 0)
        then
          let
            val imax = i+len
            fun app' i' =
                  if (i' < imax)
                  then
                    (
                      f(i', unsafeSub (array, i'));
                      app' (i'+1)
                    )
                  else ()
          in
            app' i
          end
        else raise General.Subscript

  fun foldl f init (array, i, len) =
        if (i >= 0) andalso (len >= 0)
        then
          let
            fun foldl' i' =
                  if (i' >= i)
                  then f(i', unsafeSub (array, i'), foldl' (i'-1))
                  else init
          in
            foldl' (i+len-1)
          end
        else raise General.Subscript

  fun foldr f init (array, i, len) =
        if (i >= 0) andalso (len >= 0)
        then
          let
            val imax = i+len
            fun foldr' i' =
                  if (i' < imax)
                  then f(i', unsafeSub (array, i'), foldr' (i'+1))
                  else init
          in
            foldr' i
          end
        else raise General.Subscript

  fun modify f (array, i, len) =
        if (i >= 0) andalso (len >= 0)
        then
          let
            val imax = i+len
            fun modify' i' =
                  if (i' < imax)
                  then
                    (
                      unsafeUpdate (array, i', f(i', unsafeSub (array, i')));
                      modify' (i'+1)
                    )
                  else ()
          in
            modify' i
          end
        else raise General.Subscript
end;  (* structure SparseArray *)
