(* Construct a 20041109-workalike MLton.Thread for previous MLton versions *)

structure MLton =
struct
  open MLton

  structure Thread =
  struct
    open MLton.Thread
    fun prepare (f, x) = f
  end

end
