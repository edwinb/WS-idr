module Interp

import Lang
import RawLang
import CheckLang
import Bounded

ErrMsg : Type
ErrMsg = String

doCheck : Stack k -> (i : Nat) -> Maybe (Stack i)
doCheck [] Z = Just []
doCheck [] (S k) = Nothing
doCheck (x :: xs) (S k) with (doCheck xs k)
   | Nothing = Nothing
   | Just stk = Just (x :: stk)
doCheck (x :: xs) Z = Just (Unchecked (x :: xs))
doCheck (Unchecked stk) n = doCheck stk n

drop : Stack (i + k) -> Stack k 
drop {i = Z}   stk        = stk
drop {i = S k} (x :: stk) = drop stk

getHeap : Integer -> List Integer -> Integer
getHeap 0 (x :: xs) = x
getHeap n (x :: xs) = getHeap (n - 1) xs
getHeap n []        = 0

%assert_total -- can't spot decreasing Integer
setHeap : Integer -> Integer -> List Integer -> List Integer
setHeap val 0 (x :: xs) = val :: xs
setHeap val n (x :: xs) = x :: setHeap val (n - 1) xs
setHeap val 0 [] = [val]
setHeap val n [] = if n > 0 then 0 :: setHeap val (n - 1) [] else []

%assert_total -- coverage problem
interpStk : StackInst stkIn stkOut l -> Stack stkIn ->
            IO (Stack stkOut)
interpStk (PUSH n)  stk        = return (n :: stk)
interpStk DUP       (x :: stk) = return (x :: x :: stk)
interpStk (COPY n)  stk        = let val = lookup (mkBounded n) stk in
                                     return (val :: stk)
interpStk SWAP      (x :: y :: stk) = return (y :: x :: stk)
interpStk DISCARD   (x :: stk) = return stk
interpStk (SLIDE n) (x :: stk) = return (x :: drop stk)

interpArith : ArithInst stkIn stkOut l -> Stack stkIn -> 
              IO (Stack stkOut)
interpArith ADD (x :: y :: stk) = return (y + x :: stk)
interpArith SUB (x :: y :: stk) = return (y - x :: stk)
interpArith MUL (x :: y :: stk) = return (y * x :: stk)
interpArith DIV (x :: y :: stk) = return ((y `div` x) :: stk)
interpArith MOD (x :: y :: stk) = return ((y `mod` x) :: stk)

interpHeap : HeapInst stkIn stkOut l -> Stack stkIn -> List Integer ->
             IO (Stack stkOut, List Integer)
interpHeap STORE (val :: addr :: stk) hp
    = return (stk, setHeap val addr hp)
interpHeap RETRIEVE (addr :: stk) hp
    = return (getHeap addr hp :: stk, hp)

interpFlow : FlowInst stkIn stkOut l -> 
             Prog stkOut stkOut' l ->
             LabelCache l ->
             Stack stkIn ->
             List Integer ->
             List (CallStackEntry l) -> 
             IO (Maybe (Machine l))
interpFlow (LABEL x) next lblcache stk hp cs
    = return (Just (MkMachine next lblcache (Unchecked stk) hp cs))
interpFlow (CALL x) ret lblcache stk hp cs 
    = return (Just (MkMachine (getProof (lookup x lblcache)) lblcache
                              (Unchecked stk) hp (CSE ret :: cs)))
interpFlow (JUMP x) ret lblcache stk hp cs 
    = return (Just (MkMachine (getProof (lookup x lblcache)) lblcache
                              (Unchecked stk) hp cs))
interpFlow (JZ x) next lblcache (0 :: stk) hp cs 
    = return (Just (MkMachine (getProof (lookup x lblcache)) lblcache 
                              (Unchecked stk) hp cs))
interpFlow (JZ x) next lblcache (_ :: stk) hp cs 
    = return (Just (MkMachine next lblcache stk hp cs))
interpFlow (JNEG x) next lblcache (val :: stk) hp cs 
    = if (val < 0)
         then return (Just (MkMachine (getProof (lookup x lblcache)) lblcache 
                           (Unchecked stk) hp cs))
         else return (Just (MkMachine next lblcache stk hp cs))
interpFlow RETURN _ lblcache stk hp (CSE c :: cs)
    = return (Just (MkMachine c lblcache (Unchecked stk) hp cs)) 
interpFlow RETURN _ lblcache stk hp []
    = do putStrLn "Call stack empty"
         return Nothing
interpFlow END _ lblcache stk hp cs
    = return Nothing -- TODO!

interpIO : IOInst stkIn stkOut l -> Stack stkIn -> List Integer ->
           IO (Stack stkOut, List Integer)
interpIO OUTPUT (x :: stk) hp 
     = do let c : Char = cast (prim__truncBigInt_Int x)
          putChar c
          return (stk, hp)
interpIO OUTPUTNUM (x :: stk) hp
     = do putStr (show x)
          return (stk, hp)
interpIO READCHAR (addr :: stk) hp
     = do c <- getChar
          let x : Int = cast c
          return (stk, setHeap (cast x) addr hp)
interpIO READNUM (addr :: stk) hp
     = do n <- getLine
          let x : Int = cast n
          return (stk, setHeap (cast x) addr hp)

interpInst : Machine l -> IO (Maybe (Machine l))
interpInst (MkMachine (Lang.Nil) l s h c) 
     = do putStrLn "Finished"
          return Nothing
interpInst (MkMachine (Fl END :: prog) l s h c) 
     = do putStrLn "Finished"
          return Nothing
interpInst (MkMachine (Check x' i :: prog) l s h c) 
    with (doCheck s x')
         | Just stk' = interpInst (MkMachine (i :: prog) l stk' h c)
         | Nothing   = do putStrLn ("Stack empty, need " ++ show x')
                          return Nothing
interpInst (MkMachine (Stk i :: prog) l s h c) 
     = do stk' <- interpStk i s 
          return (Just (MkMachine prog l stk' h c))
interpInst (MkMachine (Ar i :: prog) l s h c)
     = do stk' <- interpArith i s 
          return (Just (MkMachine prog l stk' h c))
interpInst (MkMachine (Hp i :: prog) l s h c)
     = do (stk', hp') <- interpHeap i s h
          return (Just (MkMachine prog l stk' hp' c))
interpInst (MkMachine (Fl i :: prog) l s h c)
     = interpFlow i prog l s h c 
interpInst (MkMachine (IOi i :: prog) l s h c)
     = do (stk', hp') <- interpIO i s h
          return (Just (MkMachine prog l stk' hp' c))

loop : Machine l -> IO ()
loop m = do x' <- interpInst m
            case x' of
                 Just m' => loop m'
                 _ => return ()



