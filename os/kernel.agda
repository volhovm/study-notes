module OS where

-- that's type and kind
* = Set₀
^ = Set₁
data ⊥ : * where

data Int : * where

data _→!_ : * → * → * where

Fd = Int

-- pointer
data ⋆ : * → * where

data List (A : *) : * where
  []   : List A
  _::_ : A → List A → List A

data  _×_ (A B : *) : * where
  _,_ : A → B → A × B

data SyscallTag : * where
  _exit : SyscallTag
  readLine : SyscallTag
  writeLine : SyscallTag
  yield : SyscallTag

Arguments : SyscallTag → *
Arguments _exit = ⊥
Arguments readLine  = ⊥
Arguments writeLine = ⊥
Arguments yield = ⊥

Result : SyscallTag → *
Result _exit = ⊥
Result readLine  = ⊥
Result writeLine = ⊥
Result yield = ⊥

record FdObj : * where

record Context : * where
  inductive
  field
   syscall : SyscallTag
   args : Arguments syscall
   cont : (Result syscall) → Context

Process : * → *
Process r = r → Context

record ProcInfo (A : *) : * where
  field
    proc : Process A
    fdtable : List (Fd × (⋆ FdObj))

Ready : * → *
Ready r = Process r × r
