
structure Syntax :> SYNTAX =
struct 

  structure L = Lib

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

  (* -------------------------------------------------------------------------- *)
  (*  Signatures                                                                *)
  (* -------------------------------------------------------------------------- *)


  structure Signat =
  struct 
    structure T = Table

    type signat = dec T.table

    val global_signat : dec T.table = T.table 100000 
    fun lookup c = T.lookup global_signat c
    fun insert (c,d) = ignore(T.insert global_signat (c,d))
    fun app f = T.appi f global_signat
    fun size() = T.size global_signat
    fun reset() = T.clear global_signat
  end

  structure Sig = Signat

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

  fun is_def c = 
      case Signat.lookup c of
        Def _ => true
      | Abbrev _ => true
      | Decl _ => false        

  fun def c = 
      case Signat.lookup c of
        Def def => #def def
      | Abbrev abb => #def abb
      | Decl _ => raise Fail "def: not a def"

  (* -------------------------------------------------------------------------- *)
  (*  Exceptions                                                                *)
  (* -------------------------------------------------------------------------- *)

  exception Fail_exp of string * exp
  exception Fail_exp2 of string * exp * exp
  exception Fail_exp_spine of string * exp * spine
  exception Fail_spine_exp of string * spine * exp
  exception Fail_hd_spine of string * head * spine
  exception Fail_sub_exp of string * sub * exp
  exception Fail_sub_exp of string * sub * exp

  (* -------------------------------------------------------------------------- *)
  (*  Eta                                                                       *)
  (* -------------------------------------------------------------------------- *)

  datatype skel = Base
                | Arrow of skel * skel

  fun card Nil = 0
    | card (App(M,S)) = 1 + card S
    | card _ = raise Fail "card: no closures"

  fun num_pi_quants (Pi {body,...}) = 1 + num_pi_quants body
    | num_pi_quants _ = 0

  fun skel_length Base = 0
    | skel_length (Arrow(_,tau)) = 1 + skel_length tau

  fun concat (Nil,M) = App(M,Nil)
    | concat (App(M,S),M') = App(M,concat(S,M'))
    | concat (SClo _,_) = raise Fail "concat: no closures"

  fun skeleton (ctx,Uni Type) = Base
    | skeleton (ctx,Root(Const a,S)) = 
      let
        val aty = exp(Sig.lookup a)
        val n = num_pi_quants aty
        val n' = card S
      in
        if n = n' then Base 
        else raise Fail "skeleton: not eta expanded"
      end
    | skeleton (ctx,Root(BVar i,S)) = 
      let
        val aty = L.ith (i-1) ctx
        val n = skel_length aty
        val n' = card S
      in
        if n = n' then Base 
        else raise Fail "skeleton: not eta expanded"
      end
    | skeleton (ctx,Pi {arg,body,...}) = 
      let
        val tau1 = skeleton(ctx,arg)
        val tau2 = skeleton(ctx,body)
      in
        Arrow(tau1,tau2)
      end
    | skeleton (_,exp) = raise Fail_exp("skeleton: bad case",exp)

  exception Fail_exp_skel of string * exp * skel 

  local
    val changed = ref false
  in


    (* A quick implementation of applying a shift substitution. 
       This is just for eta expansion, and we don't want this
       code to be tangled with the different typechecker versions.
    *)
    fun shift_head (lev,con as Const _) = con
      | shift_head (lev,var as BVar n) = 
        if n >= lev then BVar (n+1) else var

    fun shift_spine (lev,Nil) = Nil
      | shift_spine (lev,App(M,S)) = App(shift_exp(lev,M),shift_spine(lev,S))
      | shift_spine (lev,SClo _) = 
        raise Fail "shift_spine: shouldn't have closures during eta expansion"

    and shift_exp (lev,uni as (Uni _)) = uni
      | shift_exp (lev,Pi {var,arg,depend,body}) = 
        Pi {var=var,
            arg=shift_exp(lev,arg),
            depend=depend,
            body=shift_exp (lev+1,body)}
      | shift_exp (lev,Lam {var,body}) =
        Lam {var=var,body=shift_exp (lev+1,body)}
      | shift_exp (lev,Root(H,S)) = Root(shift_head (lev,H),shift_spine(lev,S))
      | shift_exp _ = 
        raise Fail "shift_exp: shouldn't have redexes or closures during eta expansion"

    fun shift_spine' exp = shift_spine(0,exp)

    fun long_exp (ctx,exp as Uni Type,Base) = exp
      | long_exp (ctx,Pi {arg,body,depend,var}, Base) =
        let
          val arg' = long_exp(ctx,arg,Base) 
          val tau = skeleton(ctx,arg')
          val body' = long_exp (tau::ctx,body,Base) 
        in
          Pi {arg=arg',body=body',depend=depend,var=var}
        end
      | long_exp (ctx,Lam {var,body},Arrow(tau1,tau2)) =
        let
          val body' = long_exp (tau1::ctx,body,tau2)
        in
          Lam {var=var,body=body'}
        end
      | long_exp (ctx,expr as Root(con as Const a,S),Base) =
        let
          val tau = skeleton (ctx,exp(Sig.lookup a))
        in
          Root(con,long_spine(ctx,S,tau))
        end
      | long_exp (ctx,exp as Root(var as BVar i,S),Base) =
        let
          val tau = L.ith (i-1) ctx (* indices start at 1 *)
        in
          Root(var,long_spine(ctx,S,tau))
        end
      | long_exp (ctx,Root(con as Const c,S),tau as Arrow(tau1,tau2)) =
        let
          val S' = concat (shift_spine' S,one)
        in
          changed := true;
          long_exp (ctx,Lam {var=NONE,body=Root(con,S')},tau)
        end
      | long_exp (ctx,Root(BVar i,S),tau as Arrow(tau1,tau2)) =
        let
          val S' = concat (shift_spine' S,one)
        in
          changed := true;
          long_exp (ctx,Lam {var=NONE,body=Root(BVar(i+1),S')},tau) 
        end
      | long_exp (_,exp,skel) = raise Fail_exp_skel("long_exp: bad case",exp,skel)

    and long_spine (ctx,Nil,Base) = Nil
      | long_spine (ctx,App(M,S),Arrow(tau1,tau2)) =
        let
          val M' = long_exp(ctx,M,tau1) 
          val S' = long_spine(ctx,S,tau2)
        in
          App(M',S')
        end
      | long_spine _ = raise Fail "long_spine: bad case"

    fun eta_expand'(e1,Uni Kind) = e1
      | eta_expand'(e1,e2) = 
        let
          val () = changed := false
          val skel = skeleton([],e2)
          val e2' = long_exp([],e1,skel)
        in
(*           if !changed then L.warning "expression is not eta long" else (); *)
          e2'
        end

    fun eta_expand e = (Timers.time Timers.eta_normal eta_expand') e

  end

end
