module instruction where

open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Bool.Base hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
open import Data.List.NonEmpty hiding (head)

open import libraries.listLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.andLib
open import libraries.maybeLib

open import stack
open import instructionBasic
open import basicBitcoinDataType




--list with all instructions
data InstructionAll : Set where
   opEqual  : InstructionAll
   opAdd    : InstructionAll
   opPush   : ℕ → InstructionAll
   opSub    : InstructionAll
   opVerify : InstructionAll
   opCheckSig : InstructionAll
   opEqualVerify : InstructionAll
   opDup : InstructionAll
   opDrop :  InstructionAll
   opSwap : InstructionAll
   opHash : InstructionAll
   opCHECKLOCKTIMEVERIFY : InstructionAll
   opCheckSig3 : InstructionAll
   opMultiSig : InstructionAll
   opIf opElse opEndIf : InstructionAll


basicInstr2Instr : InstructionBasic → InstructionAll
basicInstr2Instr opEqual = opEqual
basicInstr2Instr opAdd = opAdd
basicInstr2Instr (opPush x) = (opPush x)
basicInstr2Instr opSub = opSub
basicInstr2Instr opVerify = opVerify
basicInstr2Instr opCheckSig = opCheckSig
basicInstr2Instr opEqualVerify = opEqualVerify
basicInstr2Instr opDup = opDup
basicInstr2Instr opDrop = opDrop
basicInstr2Instr opSwap = opSwap
basicInstr2Instr opHash = opHash
basicInstr2Instr opCHECKLOCKTIMEVERIFY = opCHECKLOCKTIMEVERIFY
basicInstr2Instr opCheckSig3 = opCheckSig3
basicInstr2Instr opMultiSig = opMultiSig



BitcoinScript : Set
BitcoinScript  = List InstructionAll



basicBScript2BScript : BitcoinScriptBasic → BitcoinScript
basicBScript2BScript [] = []
basicBScript2BScript (op ∷ p) = basicInstr2Instr op ∷ basicBScript2BScript p


-- true if the instruction is not  an if then else operation
nonIfInstr : InstructionAll → Bool
nonIfInstr opIf = false
nonIfInstr opElse = false
nonIfInstr opEndIf = false
nonIfInstr op = true

NonIfInstr : InstructionAll → Set
NonIfInstr op = True (nonIfInstr op)


-- check whether a script consists of nonif instructions only
nonIfScript : BitcoinScript → Bool
nonIfScript  [] = true
nonIfScript (op ∷ rest) = nonIfInstr op ∧b nonIfScript rest

NonIfScript : BitcoinScript → Set
NonIfScript p = True (nonIfScript p)


nonIfScript2NonIf2Head : (op : InstructionAll)(rest : BitcoinScript)
                        → NonIfScript (op ∷ rest)
                        → NonIfInstr op
nonIfScript2NonIf2Head op rest p = ∧bproj₁ p


nonIfScript2NonIf2Tail : (op : InstructionAll)(rest : BitcoinScript)
                        → NonIfScript (op ∷ rest)
                        → NonIfScript rest
nonIfScript2NonIf2Tail op rest p = ∧bproj₂ p
