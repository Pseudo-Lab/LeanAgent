import Lean

/- Read the parser's original syntax positions, before macro expansion.
   This is a syntax profiler, not an elaborated dependency graph. -/
open Lean in
partial def minWalk (s : Syntax) (depth : Nat) : Elab.Command.CommandElabM Unit := do
  if let some a := s.getPos? then
    if let some b := s.getTailPos? then
      if s.getKind.toString.startsWith "Lean.Parser.Tactic." then
        logInfo m!"MIN_AST|{s.getKind}|{a.byteIdx}|{b.byteIdx}|{depth}"
  for arg in s.getArgs do
    minWalk arg (depth + 1)

elab "#min_profile " cmd:command : command => do
  minWalk cmd 0
  Lean.Elab.Command.elabCommand cmd
