val _ = OS.Process.exit
        (Server.server (CommandLine.name (),
			CommandLine.arguments ()))
