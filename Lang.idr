module Lang

import NatCmp
import Bounded
import RawLang

data StackInst : Nat -> Nat -> Nat -> Type where
     PUSH : Integer -> StackInst x (S x) lbls
     DUP  : StackInst (S x) (S (S x)) lbls
     COPY : (x : Nat) -> StackInst (plus x (S k)) (S (plus x (S k))) lbls
     SWAP : StackInst (S (S x)) (S (S x)) lbls
     DISCARD : StackInst (S x) x lbls
     SLIDE : (x : Nat) -> StackInst (S (plus x k)) (S k) lbls

data ArithInst : Nat -> Nat -> Nat -> Type where
     ADD : ArithInst (S (S x)) (S x) lbls
     SUB : ArithInst (S (S x)) (S x) lbls
     MUL : ArithInst (S (S x)) (S x) lbls
     DIV : ArithInst (S (S x)) (S x) lbls
     MOD : ArithInst (S (S x)) (S x) lbls

data HeapInst : Nat -> Nat -> Nat -> Type where
     STORE    : HeapInst (S (S x)) x lbls
     RETRIEVE : HeapInst (S x) (S x) lbls

-- For flow control, have to assume nothing on the stack at target of
-- a label
data FlowInst : Nat -> Nat -> Nat -> Type where
     LABEL  : Bounded lbls -> FlowInst x Z lbls 
     CALL   : Bounded lbls -> FlowInst x Z lbls
     JUMP   : Bounded lbls -> FlowInst x Z lbls
     JZ     : Bounded lbls -> FlowInst (S x) x lbls
     JNEG   : Bounded lbls -> FlowInst (S x) x lbls
     RETURN : FlowInst x Z lbls
     END    : FlowInst x x lbls

data IOInst : Nat -> Nat -> Nat -> Type where
     OUTPUT    : IOInst (S x) x lbls
     OUTPUTNUM : IOInst (S x) x lbls
     READCHAR  : IOInst (S x) x lbls
     READNUM   : IOInst (S x) x lbls

data Instr : Nat -> Nat -> Nat -> Type where
     Stk   : StackInst x y lbls -> Instr x y lbls
     Ar    : ArithInst x y lbls -> Instr x y lbls
     Hp    : HeapInst x y lbls -> Instr x y lbls
     Fl    : FlowInst x y lbls -> Instr x y lbls
     IOi   : IOInst x y lbls -> Instr x y lbls
     Check : (x' : Nat) -> Instr x' y lbls -> Instr x y lbls

data Prog : Nat -> Nat -> Nat -> Type where
     Nil  : Prog x x lbls
     (::) : Instr x y lbls -> Prog y z lbls -> Prog x z lbls

data Program = MkProg (Prog Z e Z)

-- testProg : Program 
-- testProg = MkProg [Check (S O) (Stk DUP),
--                    Ar ADD,
--                    IOi OUTPUTNUM,
--                    Check (S O) (IOi OUTPUTNUM)]

namespace Stack
    -- | A Stack n is a stack which has at least n things in it,
    -- but may have more
    data Stack : Nat -> Type where
         Nil   : Stack Z
         (::)  : Integer -> Stack k -> Stack (S k) 
         Unchecked : Stack k -> Stack Z

total
lookup : Bounded n -> Stack n -> Integer
lookup (Bound Z)     (x :: xs) = x
lookup (Bound (S k)) (x :: xs) = lookup (Bound k) xs

data CallStackEntry : Nat -> Type where
     CSE : Prog Z y lbls -> CallStackEntry lbls

LabelCache : Nat -> Type
LabelCache n = Vect n (out ** Prog Z out n)

record Machine : Nat -> Type where
     MkMachine : (program : Prog x y lbls) ->
                 (lblcache : LabelCache lbls) ->
                 (stack : Stack x) ->
                 (heap : List Integer) ->
                 (callstack : List (CallStackEntry lbls)) ->
                 Machine lbls

-- Setters can't be generated, too much dependecy...

setProgStack : Machine lbls -> Prog x y lbls -> Stack x -> Machine lbls
setProgStack (MkMachine _ l _ h c) p s = MkMachine p l s h c

setHeap : Machine lbls -> List Integer -> Machine lbls
setHeap (MkMachine p l s _ c) h = MkMachine p l s h c

setCallStack : Machine lbls -> List (CallStackEntry lbls) -> Machine lbls
setCallStack (MkMachine p l s h _) c = MkMachine p l s h c

