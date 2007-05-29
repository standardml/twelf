
structure Syntax : SYNTAX =
struct 

  (* -------------------------------------------------------------------------- *)
  (*  Types                                                                     *)
  (* -------------------------------------------------------------------------- *)

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

  datatype ret = RetExp of exp | RetVar of int

  structure Signat =
  struct 
    structure T = Table

    type signat = dec T.table

    val global_signat : dec T.table = T.empty 100000 
    fun lookup c = T.lookup global_signat c
    fun insert (c,d) = ignore(T.insert global_signat (c,d))
    fun app f = T.app f global_signat
    fun size() = T.size global_signat
  end

  (* -------------------------------------------------------------------------- *)
  (*  Exceptions                                                                *)
  (* -------------------------------------------------------------------------- *)

  exception Check of string
  exception Fail_exp of string * exp
  exception Fail_exp2 of string * exp * exp
  exception Fail_exp_spine of string * exp * spine
  exception Fail_spine_exp of string * spine * exp
  exception Fail_hd_spine of string * head * spine
  exception Fail_sub_exp of string * sub * exp
  exception Fail_sub_exp of string * sub * exp

  (* -------------------------------------------------------------------------- *)
  (*  Util                                                                      *)
  (* -------------------------------------------------------------------------- *)

  val expType = Uni Type
  val expKind = Uni Kind

  fun bvar n = Root(BVar n,Nil)
  val one = bvar 1
  val shift = Shift 1
  val id_sub = Shift 0

  fun id (Decl decl) = #id decl
    | id (Def def) = #id def
    | id (Abbrev abb) = #id abb

  fun name (Decl decl) = #name decl
    | name (Def def) = #name def
    | name (Abbrev abb) = #name abb

  fun exp (Decl decl) = #exp decl
    | exp (Def def) = #exp def
    | exp (Abbrev abb) = #exp abb

end
