
local 
  structure F = FunSyn
  structure I = IntSyn 
  structure S = StateSyn

  fun load file =
    case Twelf.Config.load (Twelf.Config.read file)
      of Twelf.OK => Twelf.OK
       | Twelf.ABORT => raise Domain;
	

  (* just for non-inductive types *)
  fun transformOrder' (G, Order.Arg k) = 
      let 
	val k' = (I.ctxLength G) -k+1
	val I.Dec (_, V) = I.ctxDec (G, k')
      in
	S.Arg ((I.Root (I.BVar k', I.Nil), I.id), (V, I.id))
      end
    | transformOrder' (G, Order.Lex Os) = 
        S.Lex (map (fn O => transformOrder' (G, O)) Os)
    | transformOrder' (G, Order.Simul Os) = 
        S.Simul (map (fn O => transformOrder' (G, O)) Os)

  fun transformOrder (G, F.All (F.Prim D, F), O) =
	S.All (D, transformOrder (I.Decl (G, D), F, O))
    | transformOrder (G, _, O) = transformOrder' (G, O) 
   
  fun test names =
    (let 
      val a = map (fn x => valOf (Names.nameLookup x)) names
      val [c] = a
      val name = foldr op^ "" names
      val _ = Names.varReset ()
      val F = RelFun.convertFor a
      val oldO =  Order.selLookup c handle _ => Order.Lex []
      val _ = MTPi.init (5, (F, transformOrder(I.Null, F, oldO)))
      val _ = raise Domain 
    in
      ()
    end)
in
  val _ = Twelf.chatter := 1
  val _ = FunNames.reset();

  (* Regression test for Mini-ML *)
  val _ = load "examples/mini-ml/sources.cfg"
  val _ = Twelf.loadFile "examples/mini-ml/reduce.elf"
  val _ = MTPGlobal.maxFill := 10
  val _ = test ["tps"] 
(*  val _ = test ["vs"] 


    
  val _ = load "examples/ccc/test.cfg";
  val _ = MTPGlobal.maxFill := 6
  val _ = test ["conc"]
*)
  val _ = load "examples/prop-calc/test.cfg";
  val _ = MTPGlobal.maxFill := 6
  val _ = test ["abst"]


(*
  (* Regression test for compile *)
  val _ = load "examples/compile/cpm/test.cfg"
  val _ = test ["ccp"]
  val _ = test ["peqf"]
  val _ = test ["peqr"]
*)

(* -----------------------
  val _ = load "TEST/fol.cfg";
 
  val _ = MTPGlobal.maxFill := 5
  val _ = test ["identity"]
  val _ = MTPGlobal.maxFill := 12
  val _ = test ["curry"]
(*  val _ = test ["uncurry"] 
  val _ = MTPGlobal.maxFill := 15
  val _ = test ["split"]  *)
(*  val _ = MTPGlobal.maxFill := 13
  val _ = test ["join"] *)
*)
end