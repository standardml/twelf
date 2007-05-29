
signature SYNTAX =
sig

  type const = int 

  datatype uni = Type 
               | Kind
                   
  datatype head = Const of const
                | BVar of int

  datatype depend = No | Maybe

  datatype exp = Uni of uni
               | Pi of pi
               | Lam of lam 
               | Root of head * spine
               | Redex of exp * spine
               | EClo of exp * sub

       and spine = Nil
                 | App of exp * spine
                 | SClo of spine * sub

       and sub = Dot of exp * sub
               | Shift of int
               | Comp of sub * sub

  withtype pi = {var : string option,
                 arg : exp,
                 depend : depend,
                 body : exp}

       and lam = {var : string option,
                  body : exp}

  type decl = {id : const,
               name : string,
               exp : exp,
               uni : uni}

  type def  = {id : const,
               name : string,
               exp : exp,
               def : exp,
               height : int,
               root : const,
               uni : uni}

  type abbrev = {id : const,
                 name : string,
                 exp : exp,
                 def : exp,
                 uni : uni}

  datatype dec = Decl of decl
               | Def of def
               | Abbrev of abbrev


  structure Signat :
  sig

    type signat

    (** Lookup. *)
    val lookup : const -> dec
    (** Insert. *)
    val insert : const * dec -> unit
    (** number of constants *)
    val size : unit -> int
    (** iterate a function over the signat *)
    val app : (const * dec -> unit) -> unit
    (** clear the signature*)
    val reset : unit -> unit

  end

  (* -------------------------------------------------------------------------- *)
  (*  Exceptions                                                                *)
  (* -------------------------------------------------------------------------- *)

  exception Fail_exp of string * exp
  exception Fail_exp2 of string * exp * exp
  exception Fail_exp_spine of string * exp * spine
  exception Fail_spine_exp of string * spine * exp
  exception Fail_hd_spine of string * head * spine
  exception Fail_sub_exp of string * sub * exp

  (** Eta expand an expression against a type.  
      Assumes the expressions are already beta-normal. *)
  val eta_expand : (exp * exp) -> exp

  (* -------------------------------------------------------------------------- *)
  (*  Util                                                                      *)
  (* -------------------------------------------------------------------------- *)

  val expType : exp
  val expKind : exp

  val bvar : int -> exp
  val one : exp
  val shift : sub
  val id_sub : sub

  val id : dec -> const
  val name : dec -> string
  val exp : dec -> exp
  val is_def : const -> bool
  val def : const -> exp

end
