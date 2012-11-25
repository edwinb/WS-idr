module RawLang

import NatCmp
import Bounded

Label : Set
Label = String

data RStackInst = RPUSH Integer
                | RDUP
                | RCOPY Nat
                | RSWAP
                | RDISCARD
                | RSLIDE Nat

data RArithInst = RADD | RSUB | RMUL | RDIV | RMOD

data RHeapInst = RSTORE | RRETRIEVE

data RFlowInst = RLABEL Label
               | RCALL Label
               | RJUMP Label
               | RJZ Label
               | RJNEG Label
               | RRETURN
               | REND

data RIOInst = ROUTPUT | ROUTPUTNUM | RREADCHAR | RREADNUM

data RInstr = RStk RStackInst
            | RAr RArithInst
            | RHp RHeapInst
            | RFl RFlowInst
            | RIOi RIOInst

