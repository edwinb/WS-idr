module CheckLang

import Lang
import RawLang
import NatCmp
import Bounded

checkStk : RStackInst -> (stkIn : Nat) -> (stkOut ** Instr stkIn stkOut l)
checkStk (RPUSH x) n     = (_ ** Stk (PUSH x))
checkStk RDUP      Z     = (_ ** Check (S Z) (Stk DUP))
checkStk RDUP      (S k) = (_ ** Stk DUP)
checkStk {l} (RCOPY n) m with (cmp n m)
  checkStk (RCOPY n) (n + (S k)) | CmpLT _ = (_ ** Stk (COPY n))
  checkStk {l} (RCOPY n) n           | CmpEQ   
       = let val = COPY {lbls = l} {k = Z} n in
             (S (S n) ** Check (S n) (Stk ?copyStk))
  checkStk {l} (RCOPY (m + (S k))) m | CmpGT _
       = let val = COPY {lbls = l} {k = Z} (m + (S k)) in
             (S (S (m + (S k))) ** Check (S (m + (S k))) (Stk ?copyStkGT))
checkStk RSWAP (S (S k)) = (_ ** Stk SWAP)      
checkStk RSWAP n = (_ ** Check (S (S Z)) (Stk SWAP))
checkStk RDISCARD (S k) = (_ ** Stk DISCARD)
checkStk RDISCARD n = (_ ** Check (S Z) (Stk DISCARD))
checkStk {l} (RSLIDE n) m with (cmp n m)
  checkStk {l} (RSLIDE n) (n + (S k)) | CmpLT _ 
       = let val = SLIDE {lbls=l} {k} n in
             (S k ** Stk ?slideStkLT)
  checkStk {l} (RSLIDE n) n | CmpEQ
       = let val = SLIDE {lbls=l} {k = Z} n in
             (1 ** Check (S n) (Stk ?slideStkEQ))
  checkStk {l} (RSLIDE (m + (S k))) m | CmpGT _
       = let val = SLIDE {lbls=l} {k = Z} (m + (S k)) in
             (1 ** Check (S (m + (S k))) (Stk ?slideStkGT))

checkArith : RArithInst -> (stkIn : Nat) -> (stkOut ** Instr stkIn stkOut l)
checkArith RADD (S (S k)) = (_ ** Ar ADD)
checkArith RSUB (S (S k)) = (_ ** Ar SUB)
checkArith RMUL (S (S k)) = (_ ** Ar MUL)
checkArith RDIV (S (S k)) = (_ ** Ar DIV)
checkArith RMOD (S (S k)) = (_ ** Ar MOD)
checkArith RADD n = (1 ** Check 2 (Ar ADD)) 
checkArith RSUB n = (1 ** Check 2 (Ar SUB))
checkArith RMUL n = (1 ** Check 2 (Ar MUL))
checkArith RDIV n = (1 ** Check 2 (Ar DIV))
checkArith RMOD n = (1 ** Check 2 (Ar MOD))

checkHeap : RHeapInst -> (stkIn : Nat) -> (stkOut ** Instr stkIn stkOut l)
checkHeap RSTORE (S (S k)) = (_ ** Hp STORE)
checkHeap RSTORE n         = (_ ** Check 2 (Hp STORE))
checkHeap RRETRIEVE (S k) = (_ ** Hp RETRIEVE)
checkHeap RRETRIEVE n     = (_ ** Check 1 (Hp RETRIEVE))

findLoc : Eq a => a -> Vect n a -> Maybe (Bounded n)
findLoc x [] = Nothing
findLoc x (y :: ys) 
           = if x == y then Just (Bound Z)
                       else case findLoc x ys of
                                 Just b => Just (inc b)
                                 Nothing => Nothing

checkFlow : Vect lbls Label -> RFlowInst -> (stkIn : Nat) -> 
            Maybe (stkOut ** Instr stkIn stkOut lbls)
checkFlow ls (RLABEL l) s = do bindex <- findLoc l ls
                               return (_ ** Fl (LABEL bindex))
checkFlow ls (RCALL l)  s = do bindex <- findLoc l ls
                               return (_ ** Fl (CALL bindex))
checkFlow ls (RJUMP l)  s = do bindex <- findLoc l ls
                               return (_ ** Fl (JUMP bindex))
checkFlow ls (RJZ l)    (S s) = do bindex <- findLoc l ls
                                   return (_ ** Fl (JZ bindex))
checkFlow ls (RJZ l)    s     = do bindex <- findLoc l ls
                                   return (_ ** Check 1 (Fl (JZ bindex)))
checkFlow ls (RJNEG l)  (S s) = do bindex <- findLoc l ls
                                   return (_ ** Fl (JNEG bindex))
checkFlow ls (RJNEG l)  s     = do bindex <- findLoc l ls
                                   return (_ ** Check 1 (Fl (JNEG bindex)))
checkFlow ls RRETURN    s = Just (_ ** Fl RETURN)
checkFlow ls REND       s = Just (_ ** Fl END)

checkIO : RIOInst -> (stkIn : Nat) -> (stkOut ** Instr stkIn stkOut l)
checkIO ROUTPUT    (S k) = (_ ** IOi OUTPUT)
checkIO ROUTPUTNUM (S k) = (_ ** IOi OUTPUTNUM)
checkIO ROUTPUT    n     = (_ ** Check 1 (IOi OUTPUT))
checkIO ROUTPUTNUM n     = (_ ** Check 1 (IOi OUTPUTNUM))
checkIO RREADCHAR  (S k) = (_ ** IOi READCHAR)
checkIO RREADNUM   (S k) = (_ ** IOi READNUM)
checkIO RREADCHAR  n     = (_ ** Check 1 (IOi READCHAR))
checkIO RREADNUM   n     = (_ ** Check 1 (IOi READNUM))

checkI : Vect lbls Label -> RInstr -> (stkIn : Nat) -> 
         Maybe (stkOut ** Instr stkIn stkOut lbls)
checkI ls (RStk s) stkIn = Just $ checkStk s stkIn
checkI ls (RAr s)  stkIn = Just $ checkArith s stkIn
checkI ls (RHp s)  stkIn = Just $ checkHeap s stkIn
checkI ls (RFl s)  stkIn = checkFlow ls s stkIn
checkI ls (RIOi s) stkIn = Just $ checkIO s stkIn

mkLabels : List RInstr -> (n ** Vect n Label)
mkLabels [] = (_ ** [])
-- ignore duplicate labels - behviour is undefined
mkLabels (RFl (RLABEL x) :: xs) = case mkLabels xs of
                                       (_ ** ls) => (_ ** x :: ls)
mkLabels (_ :: xs) = mkLabels xs

check' : Vect lbls Label -> List RInstr -> (stkIn : Nat) -> 
         Maybe (stkOut ** Prog stkIn stkOut lbls)
check' ls []        stk = return (_ ** [])
check' ls (i :: is) stk 
      = do (stk' ** i') <- checkI ls i stk
           (stk'' ** is') <- check' ls is stk'
           return (stk'' ** i' :: is')

findLabels : Prog x y lbls -> LabelCache lbls
findLabels {lbls} prog = updateLabels blank prog
  where
    blank : Vect n (out ** Prog Z out lbls)
    blank {n = Z} = []
    blank {n = S k} = (_ ** []) :: blank

    updateLabels : LabelCache lbls -> Prog x y lbls -> LabelCache lbls 
    updateLabels ls [] = ls
    updateLabels ls (Fl (LABEL x) :: prog)
         = updateLabels (update x (_ ** prog) ls) prog
    updateLabels ls (_ :: prog) = updateLabels ls prog


check : List RInstr -> Maybe (l ** Machine l)
check raw = do let (_ ** lbls) = mkLabels raw
               (_ ** prog) <- check' lbls raw Z
               let lblcode = findLabels prog
               return (_ ** MkMachine prog lblcode [] [] []) 

---------- Proofs ----------




CheckLang.slideStkGT = proof {
  compute;
  intro lbls,m,k;
  rewrite plusCommutative Z (plus m (S k));
  intros;
  trivial;
}

CheckLang.slideStkEQ = proof
  intro lbls,n
  rewrite plusCommutative Z n
  intros
  trivial

CheckLang.slideStkLT = proof {
  intro lbls,n,k;
  rewrite plusCommutative (S k) n;
  rewrite plusCommutative k n;
  intros;
  trivial;
}

CheckLang.copyStkGT = proof {
  intro lbls, m, k;
  compute;
  rewrite plusCommutative (S Z) (plus m (S k));
  intros;
  trivial;
}

CheckLang.copyStk = proof {
  intro lbls, n;
  rewrite plusCommutative (S Z) n;
  intros;
  trivial;
}
