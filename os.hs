{-# LANGUAGE UnicodeSyntax #-}
module OS where

data Process r = Process { process :: r → Context }
data Context = Context {
  syscall :: SyscallTag,
  args :: Arguments,
  cont :: Process (Result syscall)
  }

Result: SyscallTag → Type
Result exit = ⊥
       readLine = String
       writeLine = ⊤


data Arguments
data SyscallTag = EXIT | READLINE
