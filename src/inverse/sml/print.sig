
signature PRINT = 
sig

  val exp_to_string : sgn -> exp -> string
  val spine_to_string : sgn -> spine -> string 
  val sub_to_string : sgn -> sub -> string
  val print_exp : sgn -> exp -> unit
  val print_spine : sgn -> spine -> unit
  val print_sub : sgn -> sub -> unit

end
