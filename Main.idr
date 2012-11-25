module Main

import Parser
import Lang
import CheckLang
import Interp
import System

testProg : List RInstr 
testProg = [RFl (RLABEL "Start"), 
                  RIOi RREADNUM,
                  RStk (RPUSH 10),
                  RFl (RCALL "addup"),
                  RIOi ROUTPUTNUM,
                  RFl (RJUMP "Start"),
                  RFl (RLABEL "addup"),
                  RAr RADD,
                  RFl RRETURN]
                 

dumpIStk : StackInst x y l -> String
dumpIStk (PUSH n) = "PUSH " ++ show n
dumpIStk DUP = "DUP"
dumpIStk (COPY n) = "COPY " ++ show n
dumpIStk SWAP = "SWAP"
dumpIStk DISCARD = "DISCARD"
dumpIStk (SLIDE n) = "SLIDE " ++ show n

dumpIArith : ArithInst x y l -> String
dumpIArith ADD = "ADD"
dumpIArith SUB = "SUB"
dumpIArith MUL = "MUL"
dumpIArith DIV = "DIV"
dumpIArith MOD = "MOD"

dumpIHeap : HeapInst x y l -> String
dumpIHeap STORE = "STORE"
dumpIHeap RETRIEVE = "RETRIEVE"

dumpIFlow : FlowInst x y l -> String
dumpIFlow (LABEL x) = "LABEL " ++ show x
dumpIFlow (CALL x) = "CALL " ++ show x
dumpIFlow (JUMP x) = "JUMP " ++ show x
dumpIFlow (JZ x) = "JZ " ++ show x
dumpIFlow (JNEG x) = "JNEG " ++ show x
dumpIFlow RETURN = "RETURN"
dumpIFlow END = "END"

dumpIIO : IOInst x y l -> String
dumpIIO OUTPUT = "OUTPUT"
dumpIIO OUTPUTNUM = "OUTPUTNUM"
dumpIIO READCHAR = "READCHAR"
dumpIIO READNUM = "READNUM"

dumpI : Instr x y l -> String
dumpI (Stk i) = dumpIStk i
dumpI (Ar i) = dumpIArith i
dumpI (Hp i) = dumpIHeap i
dumpI (Fl i) = dumpIFlow i
dumpI (IOi i) = dumpIIO i
dumpI (Check x i) = "CHECK " ++ show x ++ " : " ++ dumpI i

dump : Prog x y l -> String
dump [] = ""
dump (x :: xs) = dumpI x ++ "\n" ++ dump xs

main : IO ()
main = do xs <- getArgs
          case xs of
               (_ :: prog :: _) =>
                   do src <- readFile prog
                      let raw = parse src
                      case check raw of
                           Just (_ ** m) => do -- print (dump (program m)) 
                                               loop m
                           Nothing => putStrLn "FAIL"
               _ => putStrLn "Usage: wspace <file>"

