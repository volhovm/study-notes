{-# LANGUAGE UnicodeSyntax #-}
module Pipeline where

import Data.Word
import qualified Data.Vector as V

type Vec = V.Vector

data RN = RAX | RBX | RCX | RDX | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15 | RSP | RBP | RFLAGS  -- ... maybe more

data ArgPlace = Reg RN | Mem DP

-- decoded instruction
data Instruction = Instruction { opcode :: Word8
                               , args :: [ArgPlace]
                               }

-- instruction with fetched args
data Instruction' = Instruction' { opcode' :: Word8
                                 , args' :: Vec Word64
                                 }

{--
  Assume we have Harvard arch (separate instruction/data memory)
--}
type IP     = Word64         -- instruction pointer
type DP     = Word64         -- data pointer
type MemI   = IP → Word8     -- instruction memory/L1i
type MTI    = Vec Word8   -- 'more than instruction' - encoded opcode with metadata
type RF     = RN → Word64    -- register file
type MemD   = DP → Word64    -- data memory

type StateChange = (Vec (RN, Word64), Vec (DP, Word64), IP)

fetch :: MemI → IP → MTI
fetch = undefined

decode :: MTI → Instruction
decode = undefined

fetchArgs :: RF → MemD → Instruction → Instruction'
fetchArgs rf memd i = Instruction' (opcode i) $ V.fromList $ map getA (args i)
    where getA (Reg r) = rf r
          getA (Mem m) = memd m

exec :: Instruction' → StateChange
exec = undefined

commit :: RF → MemD → IP → StateChange → (RF, MemD, IP)
commit = undefined
