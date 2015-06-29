module OS where


-- that's type and kind
* = Set₀
^ = Set₁
data ⊥ : ^ where

data SyscallTag : * where
  _exit : SyscallTag
  readLine : SyscallTag
  writeLine : SyscallTag
  yield : SyscallTag

Arguments : SyscallTag → ^
Arguments _exit = ⊥
Arguments readLine  = ⊥
Arguments writeLine = ⊥
Arguments yield = ⊥

Result : SyscallTag → ^
Result _exit = ⊥
Result readLine  = ⊥
Result writeLine = ⊥
Result yield = ⊥

record Context : ^ where
  inductive
  field
   syscall : SyscallTag
   args : Arguments syscall
   cont : (Result syscall) → Context
