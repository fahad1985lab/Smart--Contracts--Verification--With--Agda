module instructionBasic where

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
open import basicBitcoinDataType


--list with normal instructions

data InstructionBasic : Set where
  opEqual opAdd opSub opVerify opEqualVerify opDrop opSwap opDup    : InstructionBasic
  opHash opMultiSig opCHECKLOCKTIMEVERIFY opCheckSig3 opCheckSig    : InstructionBasic
  opPush                                                            : ℕ → InstructionBasic



BitcoinScriptBasic : Set
BitcoinScriptBasic  = List InstructionBasic
