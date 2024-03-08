/-
Copyright (c) 2024 The LeanSAT Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

namespace LeanSAT.Util

def mkFIFO (path : System.FilePath) : IO Unit := do
  let child ← IO.Process.spawn {
    cmd := "mkfifo"
    args := #[path.toString]
  }
  if (← child.wait) > 0 then
    throw (IO.userError "mkfifo failed")

def getTempPath : IO System.FilePath := do
  let name ← IO.Process.run {
    cmd := "mktemp"
    args := #["-u"]
  }
  return name.trim

def withTempFIFO (f : System.FilePath → IO α) : IO α := do
  let name ← getTempPath
  mkFIFO name
  let res ← f name
  IO.FS.removeFile name
  return res
