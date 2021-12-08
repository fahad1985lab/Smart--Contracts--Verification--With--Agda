open import basicBitcoinDataType

module verificationP2PKHbasic (param : GlobalParameters) where

open import libraries.listLib
open import Data.List.Base
open import libraries.natLib
open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_)
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; _<_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_ ; _<_)
open import Data.List.NonEmpty hiding (head )
open import Data.Nat using (ℕ; _+_; _≥_; _>_; zero; suc; s≤s; z≤n)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality


open import libraries.andLib
open import libraries.miscLib
open import libraries.maybeLib
open import libraries.boolLib

open import stack
open import stackPredicate
open import instruction
open import instructionBasic

open import semanticBasicOperations param


instruction-1 : InstructionBasic
instruction-1 = opCheckSig

instruction-2 : InstructionBasic
instruction-2 = opVerify

instruction-3 : InstructionBasic
instruction-3 = opEqual

instruction-4 : ℕ →  InstructionBasic
instruction-4 pbkh = opPush  pbkh

instruction-5 : InstructionBasic
instruction-5 = opHash

instruction-6 : InstructionBasic
instruction-6 = opDup

accept-0Basic : StackPredicate
accept-0Basic = acceptStateˢ

--acceptone
acceptˢ₁ : StackPredicate
acceptˢ₁ time m [] = ⊥
acceptˢ₁ time m (sig ∷ []) = ⊥
acceptˢ₁ time m ( pubKey  ∷ sig ∷ st) = IsSigned m  sig pubKey

acceptˢ₂Core : Time → Msg → ℕ → ℕ → ℕ → Set
acceptˢ₂Core time m zero pubKey sig = ⊥
acceptˢ₂Core time m (suc x) pubKey sig =  IsSigned  m sig pubKey

--acceptTwo
acceptˢ₂ : StackPredicate
acceptˢ₂ time m [] = ⊥
acceptˢ₂ time m (x ∷ []) = ⊥
acceptˢ₂ time m (x ∷ x₁ ∷ []) = ⊥
acceptˢ₂ time m (x ∷ pubKey ∷ sig ∷ rest) = acceptˢ₂Core time m x pubKey sig


--acceptThree
acceptˢ₃ : StackPredicate
acceptˢ₃ time m [] = ⊥
acceptˢ₃ time m (x ∷ []) = ⊥
acceptˢ₃ time m (x ∷ x₁ ∷ []) = ⊥
acceptˢ₃ time m (x ∷ x₁ ∷ x2 ∷ []) = ⊥
acceptˢ₃ time m (pbkh2 ∷ pbkh1 ∷ pubKey ∷ sig ∷ rest)
     =  (pbkh2 ≡  pbkh1) ∧ IsSigned  m sig pubKey


--acceptFour
acceptˢ₄ : ( pubKey : ℕ ) → StackPredicate
acceptˢ₄ pbkh1 time m [] = ⊥
acceptˢ₄ pbkh1 time m (x ∷ []) = ⊥
acceptˢ₄ pbkh1 time m (x ∷ x1  ∷ []) = ⊥
acceptˢ₄ pbkh1 time m ( pbkh2   ∷ pubKey ∷ sig ∷ st)
        = (pbkh2 ≡  pbkh1) ∧  IsSigned  m sig pubKey


--acceptFive
acceptˢ₅ : ( pubKey : ℕ ) → StackPredicate
acceptˢ₅  pbkh1 time m [] = ⊥
acceptˢ₅  pbkh1 time m (x ∷ []) = ⊥
acceptˢ₅  pbkh1 time m (x ∷ x₁ ∷ []) = ⊥
acceptˢ₅  pbkh1 time m ( pubKey1   ∷ pubKey ∷ sig ∷ st)
       =  (hashFun pubKey1 ≡  pbkh1) ∧  IsSigned   m  sig  pubKey


--weakestprecondition
wPreCondP2PKHˢ : (pbkh : ℕ ) → StackPredicate
wPreCondP2PKHˢ  pbkh  time  m  []                    =  ⊥
wPreCondP2PKHˢ  pbkh  time  m  (x ∷ [])              =  ⊥
wPreCondP2PKHˢ  pbkh  time  m  ( pubKey ∷ sig ∷ st)  =
                (hashFun pubKey ≡  pbkh ) ∧ IsSigned  m sig pubKey



correct3Aux1 : (x : ℕ)(rest : List ℕ)(time : Time)(msg : Msg) → acceptˢ₂ time msg (x ∷ rest)
               →  isTrueNat x
correct3Aux1 zero (zero ∷ []) time msg accept = accept
correct3Aux1 zero (zero ∷ x ∷ rest) time msg accept = accept
correct3Aux1 zero (suc x ∷ []) time msg accept = accept
correct3Aux1 zero (suc x ∷ x₁ ∷ rest) time msg accept = accept
correct3Aux1 (suc x) (x₁ ∷ rest) time msg accept = tt


correct3Aux2 : ( x pubKey sig : ℕ )( rest : List ℕ)(time : Time)(m : Msg)
                → acceptˢ₂ time m (x ∷ pubKey ∷ sig ∷ rest)
                → IsSigned  m sig pubKey
correct3Aux2 (suc x) pubkey sig rest time m accept = accept



lemmaCorrect3From1 : (x z t : ℕ)(time : Time )(m : Msg)
                    →  acceptˢ₂Core time m x z t → isTrueNat x
lemmaCorrect3From1 (suc x) z t time m p = tt


lemmaCorrect3From : (x y z t : ℕ)(time : Time)(m : Msg)
                    →  acceptˢ₂Core time m (compareNaturals x y) z t → x ≡ y
lemmaCorrect3From x y z t time m p = compareNatToEq x  y (lemmaCorrect3From1 (compareNaturals x y) z t time m p)


script-1-b  : BitcoinScriptBasic
script-1-b = opCheckSig ∷ []

script-2-b : BitcoinScriptBasic
script-2-b = opVerify ∷ script-1-b

script-3-b : BitcoinScriptBasic
script-3-b = opEqual ∷ script-2-b

script-4-b : ℕ → BitcoinScriptBasic
script-4-b pbkh  =  opPush  pbkh ∷ script-3-b

script-5-b : ℕ →  BitcoinScriptBasic
script-5-b pbkh = opHash  ∷ script-4-b  pbkh

script-6-b : ℕ → BitcoinScriptBasic
script-6-b pbkh  = opDup ∷ script-5-b pbkh


--new
script-7-b : ℕ → BitcoinScriptBasic
script-7-b pbkh = opMultiSig ∷ script-6-b pbkh

script-7'-b : (pbkh pbk1 pbk2 : ℕ) → BitcoinScriptBasic
script-7'-b pbkh pbk1 pbk2 = opMultiSig ∷ script-6-b pbkh


script-1  : BitcoinScript
script-1  = basicBScript2BScript script-1-b

script-2  : BitcoinScript
script-2  = basicBScript2BScript script-2-b

script-3  : BitcoinScript
script-3  = basicBScript2BScript script-3-b

script-4  : ℕ → BitcoinScript
script-4  pbk = basicBScript2BScript (script-4-b pbk)

script-5  : ℕ → BitcoinScript
script-5  pbk = basicBScript2BScript (script-5-b pbk)

script-6  : ℕ → BitcoinScript
script-6  pbk = basicBScript2BScript (script-6-b pbk)

script-7  : ℕ → BitcoinScript
script-7  pbk = basicBScript2BScript (script-7-b pbk)


script-7' : (pbkh pbk1 pbk2 : ℕ) → BitcoinScript
script-7'  pbkh pbk1 pbk2 = basicBScript2BScript (script-7'-b pbkh pbk1 pbk2)



instructionsBasic : (pbkh : ℕ) (n : ℕ) → n ≤ 5 → InstructionBasic
instructionsBasic pbkh 0 _ = opCheckSig
instructionsBasic pbkh 1 _ = opVerify
instructionsBasic pbkh 2 _ = opEqual
instructionsBasic pbkh 3 _ = opPush pbkh
instructionsBasic pbkh 4 _ = opHash
instructionsBasic pbkh 5 _ = opDup

scriptP2PKH : (pbkh : ℕ) → BitcoinScript
scriptP2PKH pbkh = opDup ∷ opHash ∷ (opPush pbkh) ∷ opEqual ∷ opVerify ∷ opCheckSig ∷ []

weakestPreConditionP2PKH-basis : (pbkh : ℕ) → StackPredicate
weakestPreConditionP2PKH-basis = wPreCondP2PKHˢ
