structure Run = struct

  val argv = CommandLine.arguments()

  val stat = RegressionTest.process(List.nth(argv,List.length(argv) - 1))
  val _ = OS.Process.exit stat

end
