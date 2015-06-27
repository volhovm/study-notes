{-# LANGUAGE UnicodeSyntax #-}
module OS where

data Process r = Process { process :: r → Context }
data Context = Context {
  syscall :: SyscallTag
  args :: Arguments
  cont :: Process r → (Result syscall)
                       }
data Argumentsg
data SyscallTag = _exit | readLine
