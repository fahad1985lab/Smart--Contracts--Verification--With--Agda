

module verificationStackScripts.stackInstruction where


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
open import libraries.miscLib
open import libraries.maybeLib


open import basicBitcoinDataType
open import stack
open import verificationStackScripts.stackState
open import verificationStackScripts.sPredicate


{-
--list with normal instructions
data InstructionBasic : Set where
  opEqual  : Instruction
  opAdd    : Instruction
  opPush   : ℕ → Instruction
  opSub    : Instruction
  opVerify : Instruction
  opCheckSig : Instruction
  opEqualVerify : Instruction
  opDup : Instruction
  opDrop :  Instruction
  opSwap  : Instruction
  opHash : Instruction
  opCHECKLOCKTIMEVERIFY : Instruction
  opCheckSig3 : Instruction
  opMultiSig : Instruction



BitcoinScriptBasic : Set
BitcoinScriptBasic  = List Instruction
-}
