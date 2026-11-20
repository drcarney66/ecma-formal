module

public import Engine.Cli.Run

@[expose] public section

/-! # `ecma-run`'s root: `Engine.Cli.main` with the default options. -/

def main (args : List String) : IO UInt32 := Engine.Cli.main {} args
