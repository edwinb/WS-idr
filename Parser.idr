module Parser

import RawLang
import Debug.Trace

{-
mspan : (a -> Bool) -> List a -> (List a, List a)
mspan p xs = (takeWhile p xs, dropWhile p xs)
-}

mspan : Show a => (a -> Bool) -> List a -> (List a, List a)
mspan p []      = ([], [])
mspan p (x::xs) =
  if p x then
    let (ys, zs) = mspan p xs in
      (x::ys, zs)
  else
    ([], x::xs)

parseNum : List Char -> (Integer, List Char)
parseNum xs = case (span isWDigit xs) of
                   (num, (_ :: rest)) => (process 0 1 (reverse num), rest)
                   (num, []) => (process 0 1 (reverse num), [])
  where
    isWDigit ' ' = True
    isWDigit '\t' = True
    isWDigit _ = False

    process : Integer -> Integer -> List Char -> Integer
    process acc p (' '::xs) = process acc (2 * p) xs
    process acc p ('\t'::xs) = process (acc + p) (2 * p) xs
    process acc p (_ :: xs) = process acc (2 * p) xs
    process acc p _ = acc

parseLbl : List Char -> (String, List Char)
parseLbl xs = case (span isWDigit xs) of
                   (arg, (_ :: rest)) => (process "" arg, rest)
                   (arg, []) => (process "" arg, [])
  where
    isWDigit ' ' = True
    isWDigit '\t' = True
    isWDigit _ = False

    process : String -> List Char -> String
    process acc (c :: xs) = process (acc ++ strCons c "") xs
    process acc _ = acc

parse' : List Char -> List RInstr
parse' (' '::' '::xs) = case parseNum xs of
                           (num, rest) => RStk (RPUSH num) :: parse' rest
parse' (' '::'\n'::' '::xs) = RStk RDUP :: parse' xs
parse' (' '::'\t'::' '::xs) 
                      = case parseNum xs of
                           (num, rest) => 
                              RStk (RCOPY (fromInteger num)) :: parse' rest
parse' (' '::'\n'::'\t'::xs) = RStk RSWAP :: parse' xs
parse' (' '::'\n'::'\n'::xs) = RStk RDISCARD :: parse' xs
parse' (' '::'\t'::'\n'::xs) 
                      = case parseNum xs of
                           (num, rest) => 
                              RStk (RSLIDE (fromInteger num)) :: parse' rest

parse' ('\t'::' '::' '::' '::xs) = RAr RADD :: parse' xs
parse' ('\t'::' '::' '::'\t'::xs) = RAr RSUB :: parse' xs
parse' ('\t'::' '::' '::'\n'::xs) = RAr RMUL :: parse' xs
parse' ('\t'::' '::'\t'::' '::xs) = RAr RDIV :: parse' xs
parse' ('\t'::' '::'\t'::'\t'::xs) = RAr RMOD :: parse' xs

parse' ('\t'::'\t'::' '::xs) = RHp RSTORE :: parse' xs
parse' ('\t'::'\t'::'\t'::xs) = RHp RRETRIEVE :: parse' xs

parse' ('\n'::' '::' '::xs) 
    = case parseLbl xs of
           (lbl, rest) => RFl (RLABEL lbl) :: parse' rest
parse' ('\n'::' '::'\t'::xs) 
    = case parseLbl xs of
           (lbl, rest) => RFl (RCALL lbl) :: parse' rest
parse' ('\n'::' '::'\n'::xs) 
    = case parseLbl xs of
           (lbl, rest) => RFl (RJUMP lbl) :: parse' rest
parse' ('\n'::'\t'::' '::xs) 
    = case parseLbl xs of
           (lbl, rest) => RFl (RJZ lbl) :: parse' rest
parse' ('\n'::'\t'::'\t'::xs) 
    = case parseLbl xs of
           (lbl, rest) => RFl (RJNEG lbl) :: parse' rest
parse' ('\n'::'\t'::'\n'::xs) = RFl RRETURN :: parse' xs
parse' ('\n'::'\n'::'\n'::xs) = RFl REND :: parse' xs

parse' ('\t'::'\n'::' '::' '::xs) = RIOi ROUTPUT :: parse' xs
parse' ('\t'::'\n'::' '::'\t'::xs) = RIOi ROUTPUTNUM :: parse' xs
parse' ('\t'::'\n'::'\t'::' '::xs) = RIOi RREADCHAR :: parse' xs
parse' ('\t'::'\n'::'\t'::'\t'::xs) = RIOi RREADNUM :: parse' xs

parse' xs = []

dumpChar : Char -> String
dumpChar ' ' = "__ "
dumpChar '\t' = "|| "
dumpChar '\n' = "++ "
dumpChar _ = "XX "

dumpInput : Nat -> List Char -> String
dumpInput Z xs = "\n" ++ dumpInput 16 xs
dumpInput (S k) (x :: xs) = dumpChar x ++ dumpInput k xs
dumpInput _ _ = ""

parse : String -> List RInstr
parse x = parse' (filter isSpace (unpack x))



