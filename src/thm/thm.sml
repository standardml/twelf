structure ThmSyn = 
  ThmSyn ((*! structure IntSyn = IntSyn !*)
	  (*! structure ModeSyn' = ModeSyn !*)
	  structure Abstract = Abstract
	  structure Whnf = Whnf
	  structure Paths' = Paths
	  structure Names' = Names);

structure ThmPrint =
  ThmPrint (structure ThmSyn' = ThmSyn
	    structure Formatter = Formatter);

structure Thm =
  Thm (structure Global = Global
       structure ThmSyn' = ThmSyn
       structure TabledSyn = TabledSyn
(*       structure RedOrder = RedOrder *) (* -bp *)
       structure Order = Order
       structure ModeTable = ModeTable
       structure ThmPrint = ThmPrint
       structure Paths' = Paths);
