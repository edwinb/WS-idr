module Bounded

-- Various operations on bounded natural numbers 
--  * vector lookup
--  * increase/decrease bounds
--  * checked addition/increment

import NatCmp

%default total

-- | Bounded natural numbers
data Bounded : Nat -> Type where
     Bound : (k : Nat) -> Bounded (plus (S k) n)

instance Show (Bounded n) where
     show = show' where
        show' : Bounded n' -> String
        show' (Bound k) = show k

mkBounded : (k : Nat) -> Bounded (plus k (S n))
mkBounded {n} k ?= Bound {n} k

lookup : Bounded n -> Vect a n -> a
lookup (Bound O)     (x :: xs) = x
lookup (Bound (S k)) (x :: xs) = lookup (Bound k) xs

update : Bounded n -> a -> Vect a n -> Vect a n
update (Bound O)     val (x :: xs) = val :: xs
update (Bound (S k)) val (x :: xs) = x :: update (Bound k) val xs

weaken : Bounded n -> Bounded (S n)
weaken (Bound {n} k) ?= Bound {n = S n} k

weakenP : Bounded n -> Bounded (n + m)
weakenP {m} (Bound {n} k) ?= Bound {n = n + m} k

strengthen : Bounded (S n) -> Either (Bounded (S n)) (Bounded n)
strengthen (Bound {n = O} x) = Left (Bound x)
strengthen (Bound {n = S k} x) = ?strengthenOK

inBound : Nat -> (b : Nat) -> Maybe (Bounded b)
inBound x b with (cmp x b)
  inBound x (x + S y) | cmpLT y = Just ?inBoundOK
  inBound x x         | cmpEQ   = Nothing
  inBound (y + S k) y | cmpGT k = Nothing

(+) : Bounded n -> Bounded n -> Maybe (Bounded n)
(+) a b = plusB a b refl where
  plusB : Bounded x -> Bounded y -> (x = y) -> Maybe (Bounded x)
  plusB (Bound a) (Bound b) p = inBound (a + b) _

inc : Bounded n -> Bounded (S n)
inc (Bound x) = Bound (S x)

safeinc : Bounded n -> Either (Bounded (S n)) (Bounded n)
safeinc (Bound {n = O} x) = Left (Bound (S x))
safeinc (Bound {n = S k} x) = ?incOK

---------- Proofs ----------

Bounded.weakenP_lemma_1 = proof {
  compute;
  intros;
  rewrite plusAssociative k n m;
  trivial;
}

Bounded.weaken_lemma_1 = proof {
  intros;
  rewrite sym (plusSuccRightSucc k n);
  trivial;
}

Bounded.mkBounded_lemma_1 = proof {
  intros;
  rewrite plusCommutative (S n) k;
  rewrite plusCommutative k n;
  trivial;
}

Bounded.incOK = proof {
  intros;
  refine Right;
  rewrite plusSuccRightSucc x k;
  exact (Bound (S x));
}

Bounded.inBoundOK = proof {
  intros;
  compute;
  rewrite plusCommutative (S y) x;
  rewrite plusCommutative x y;
  exact (Bound x);
}

Bounded.strengthenOK = proof {
  intros;
  refine Right;
  rewrite plusCommutative (S k) x;
  rewrite plusCommutative x k;
  refine Bound;
  exact x;
}

