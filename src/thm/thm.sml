structure ThmSyn = 
  ThmSyn (structure IntSyn = IntSyn
	  structure ModeSyn' = ModeSyn
	  structure Abstract = Abstract
	  structure Whnf = Whnf
	  structure Paths' = Paths);

structure ThmPrint =
  ThmPrint (structure ThmSyn' = ThmSyn
	    structure Formatter = Formatter);

structure Thm =
  Thm (structure Global = Global
       structure ThmSyn' = ThmSyn
(*       structure RedOrder = RedOrder *) (* -bp *)
       structure Order = Order
       structure ModeSyn' = ModeSyn
       structure ThmPrint = ThmPrint
       structure Paths' = Paths);
