open import basicBitcoinDataType

module verificationMultiSig (param : GlobalParameters) where


open import Data.List.Base hiding (_++_ )
open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_  )
open import Data.Sum
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Maybe
--open import Data.List.Base
open import Data.Bool  hiding (_≤_ ; _<_ ; if_then_else_  )  renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_ ; _<_)
open import Data.List.NonEmpty hiding (head; [_])
open import Data.Nat using (ℕ; _+_; _≥_; _>_; zero; suc; s≤s; z≤n)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality
--open import Agda.Builtin.Equality.Rewrite

open import libraries.listLib
open import libraries.emptyLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.equalityLib



open import libraries.andLib
open import libraries.miscLib
open import libraries.maybeLib

open import stack
open import stackPredicate
open import instructionBasic
open import semanticBasicOperations param
open import stackSemanticsInstructions param
open import hoareTripleStack param

-------------------------------------------------------
-- Verification of the Multisig script both for active and nonactive ifStack
--  theoremCorrectnessMultiSig-2-3   proves correctness for active ifStack
--  theoremCorrectnessMultiSig-2-3-nonactive proves correctness for nonactive ifStack
-----------------------------------------------------------------






weakestPreConditionMultiSig-2-3-bas : (pbk1 pbk2 pbk3 :  ℕ)
                                      → StackPredicate
weakestPreConditionMultiSig-2-3-bas pbk1 pbk2 pbk3 time msg₁ [] = ⊥
weakestPreConditionMultiSig-2-3-bas pbk1 pbk2 pbk3 time msg₁ (x ∷ []) = ⊥
weakestPreConditionMultiSig-2-3-bas pbk1 pbk2 pbk3 time msg₁ (x ∷ y ∷ []) = ⊥
weakestPreConditionMultiSig-2-3-bas pbk1 pbk2 pbk3 time msg₁ (sig2 ∷ sig1 ∷ dummy ∷ stack₁) =
         ( (IsSigned msg₁ sig1 pbk1 ∧  IsSigned msg₁ sig2 pbk2) ⊎
          (IsSigned msg₁ sig1 pbk1 ∧  IsSigned msg₁ sig2 pbk3) ⊎
          (IsSigned msg₁ sig1 pbk2 ∧  IsSigned msg₁ sig2 pbk3 ))


multiSigScript-2-3-b : (pbk1 pbk2 pbk3 :  ℕ) → BitcoinScriptBasic
multiSigScript-2-3-b pbk1 pbk2 pbk3 = (opPush 2) ∷ (opPush pbk1) ∷  (opPush pbk2) ∷  (opPush pbk3) ∷  (opPush 3) ∷   opMultiSig ∷ []

lemmaHoareTripleStackGeAux'1 : (msg₂ : Msg)
                               (pbk1 pbk2 pbk3 sig1 sig2 : ℕ)
                               → True (isSigned  msg₂ sig1 pbk1)
                              →  True (isSigned  msg₂ sig2 pbk2)
                               → True (compareSigsMultiSig msg₂ ( sig1 ∷ sig2 ∷ []) (pbk1 ∷ pbk2 ∷ pbk3 ∷ []))

lemmaHoareTripleStackGeAux'1 msg₂ pbk1 pbk2 pbk3 sig1 sig2 x x₁ with  (isSigned  msg₂ sig1 pbk1)
lemmaHoareTripleStackGeAux'1 msg₂ pbk1 pbk2 pbk3 sig1 sig2 x x₁ | true  with (isSigned  msg₂ sig2 pbk2)
lemmaHoareTripleStackGeAux'1 msg₂ pbk1 pbk2 pbk3 sig1 sig2 x x₁ | true | true = tt




lemmaHoareTripleStackGeAux'2 : (msg₂ : Msg)
                               (pbk1 pbk2 pbk3 sig1 sig2 : ℕ)
                               → True  (isSigned  msg₂ sig1 pbk1)
                              →  True (isSigned  msg₂ sig2 pbk3)
                               → True (compareSigsMultiSig msg₂ ( sig1 ∷ sig2 ∷ []) (pbk1 ∷ pbk2 ∷ pbk3 ∷ []))
lemmaHoareTripleStackGeAux'2 msg₂ pbk1 pbk2 pbk3 sig1 sig2 x x₁ with (isSigned  msg₂ sig1 pbk1)
lemmaHoareTripleStackGeAux'2 msg₂ pbk1 pbk2 pbk3 sig1 sig2 x x₁ | true with (isSigned  msg₂ sig2 pbk2)
lemmaHoareTripleStackGeAux'2 msg₂ pbk1 pbk2 pbk3 sig1 sig2 x x₁ | true | false with (isSigned  msg₂ sig2 pbk3)
lemmaHoareTripleStackGeAux'2 msg₂ pbk1 pbk2 pbk3 sig1 sig2 x x₁ | true | false | true = tt
lemmaHoareTripleStackGeAux'2 msg₂ pbk1 pbk2 pbk3 sig1 sig2 x x₁ | true | true = tt



lemmaHoareTripleStackGeAux'3 : (msg₂ : Msg)
                               (pbk1 pbk2 pbk3 sig1 sig2 : ℕ)
                               → True (isSigned  msg₂ sig1 pbk2)
                              →  True (isSigned  msg₂ sig2 pbk3)
                               → True (compareSigsMultiSig msg₂ ( sig1 ∷ sig2 ∷ []) (pbk1 ∷ pbk2 ∷ pbk3 ∷ []))
lemmaHoareTripleStackGeAux'3 msg₂ pbk1 pbk2 pbk3 sig1 sig2 x x₁  with (isSigned  msg₂ sig1 pbk1 )
lemmaHoareTripleStackGeAux'3 msg₂ pbk1 pbk2 pbk3 sig1 sig2 x x₁ | false with (isSigned  msg₂ sig1 pbk2)
lemmaHoareTripleStackGeAux'3 msg₂ pbk1 pbk2 pbk3 sig1 sig2 x x₁ | false | true with isSigned  msg₂ sig2 pbk3
lemmaHoareTripleStackGeAux'3 msg₂ pbk1 pbk2 pbk3 sig1 sig2 x x₁ | false | true | true = tt
lemmaHoareTripleStackGeAux'3 msg₂ pbk1 pbk2 pbk3 sig1 sig2 x x₁ | true with (isSigned  msg₂ sig2 pbk2)
lemmaHoareTripleStackGeAux'3 msg₂ pbk1 pbk2 pbk3 sig1 sig2 x x₁ | true | false with (isSigned  msg₂ sig2 pbk3)
lemmaHoareTripleStackGeAux'3 msg₂ pbk1 pbk2 pbk3 sig1 sig2 x x₁ | true | false | true = tt
lemmaHoareTripleStackGeAux'3 msg₂ pbk1 pbk2 pbk3 sig1 sig2 x x₁ | true | true = tt

{-
For the other direction we get the goal


Goal: (True (isSigned  msg₂ sig1 pbk1 ) ∧
       True (isSigned  msg₂ sig2 pbk2))
      ⊎
      (True (isSigned  msg₂ sig1 pbk1 ) ∧
       True (isSigned  msg₂ sig2 pbk3))
      ⊎
      (True (isSigned  msg₂ sig1 pbk2) ∧
       True (isSigned  msg₂ sig2 pbk3))
————————————————————————————————————————————————————————————
x     : True
        (notFalse
         (boolToNat
          (compareSigsMultiSigAux msg₂ (sig2 ∷ []) (pbk2 ∷ pbk3 ∷ []) sig1
           (isSigned  msg₂ sig1 pbk1 ))))



Again we use the boolToNatNotFalseLemma2 lemma to get rid of the
True(notFalse (boolToNat

and show
lemmaHoareTripleStackGeAux'4

we see that now the x ends with
(isSigned  msg₂ sig1 pbk1 )
so we start with the with pattern with a case distinction on this
and continue making casedistintion on the last formula in x



-}

lemmaHoareTripleStackGeAux'4 : (msg₂ : Msg)
         (pbk1 pbk2 pbk3 sig1 sig2 : ℕ)
          → True (compareSigsMultiSigAux msg₂ (sig2 ∷ []) (pbk2 ∷ pbk3 ∷ [])  sig1
                 (isSigned  msg₂ sig1 pbk1 ))
          →     (True (isSigned  msg₂ sig1 pbk1 ) ∧ True (isSigned  msg₂ sig2 pbk2))
             ⊎  (True (isSigned  msg₂ sig1 pbk1 ) ∧  True (isSigned  msg₂ sig2 pbk3))
             ⊎  (True (isSigned  msg₂ sig1 pbk2) ∧ True (isSigned  msg₂ sig2 pbk3))
lemmaHoareTripleStackGeAux'4 msg₂ pbk1 pbk2 pbk3 sig1 sig2 p with (isSigned  msg₂ sig1 pbk1 )
lemmaHoareTripleStackGeAux'4 msg₂ pbk1 pbk2 pbk3 sig1 sig2 p | false with (isSigned  msg₂ sig1 pbk2)
lemmaHoareTripleStackGeAux'4 msg₂ pbk1 pbk2 pbk3 sig1 sig2 p | false | false with (isSigned  msg₂ sig1 pbk3)
lemmaHoareTripleStackGeAux'4 msg₂ pbk1 pbk2 pbk3 sig1 sig2 () | false | false | false
lemmaHoareTripleStackGeAux'4 msg₂ pbk1 pbk2 pbk3 sig1 sig2 () | false | false | true
lemmaHoareTripleStackGeAux'4 msg₂ pbk1 pbk2 pbk3 sig1 sig2 p | false | true with (isSigned  msg₂ sig2 pbk3)
lemmaHoareTripleStackGeAux'4 msg₂ pbk1 pbk2 pbk3 sig1 sig2 p | false | true | true = inj₂ (inj₂ (conj tt tt))
lemmaHoareTripleStackGeAux'4 msg₂ pbk1 pbk2 pbk3 sig1 sig2 p | true  with (isSigned  msg₂ sig2 pbk2)
lemmaHoareTripleStackGeAux'4 msg₂ pbk1 pbk2 pbk3 sig1 sig2 p | true | false with (isSigned  msg₂ sig2 pbk3)
lemmaHoareTripleStackGeAux'4 msg₂ pbk1 pbk2 pbk3 sig1 sig2 p | true | false | true = inj₂ (inj₁ (conj tt tt))
lemmaHoareTripleStackGeAux'4 msg₂ pbk1 pbk2 pbk3 sig1 sig2 p | true | true = inj₁ (conj tt tt)






weakestPreConditionMultiSig-2-4ˢ : (pbk1 pbk2 pbk3 pbk4 :  ℕ)
                                      → StackPredicate
weakestPreConditionMultiSig-2-4ˢ pbk1 pbk2 pbk3 pbk4 time  msg₁ [] = ⊥
weakestPreConditionMultiSig-2-4ˢ pbk1 pbk2 pbk3 pbk4 time  msg₁ (x ∷ []) = ⊥
weakestPreConditionMultiSig-2-4ˢ pbk1 pbk2 pbk3 pbk4 time  msg₁ (x ∷ y ∷ []) = ⊥
weakestPreConditionMultiSig-2-4ˢ pbk1 pbk2 pbk3 pbk4 time  msg₁ ( sig2 ∷ sig1 ∷ dummy ∷ stack₁) =
       (  (IsSigned msg₁ sig1 pbk1 ∧  IsSigned msg₁ sig2 pbk2) ⊎
          (IsSigned msg₁ sig1 pbk1 ∧  IsSigned msg₁ sig2 pbk3) ⊎
          (IsSigned msg₁ sig1 pbk1 ∧  IsSigned msg₁ sig2 pbk4) ⊎
          (IsSigned msg₁ sig1 pbk2 ∧  IsSigned msg₁ sig2 pbk3) ⊎
          (IsSigned msg₁ sig1 pbk2 ∧  IsSigned msg₁ sig2 pbk4) ⊎
          (IsSigned msg₁ sig1 pbk3 ∧  IsSigned msg₁ sig2 pbk4))





HoareTripleStackGeAux' : (msg₁ : Msg)(pbk1 pbk2 pbk3 : ℕ) →
                 < (weakestPreConditionMultiSig-2-3-bas pbk1 pbk2 pbk3) >gˢ
                 (λ time₁ msg₁ stack →
                    executeMultiSig3 msg₁ (pbk1 ∷ pbk2 ∷ pbk3 ∷ []) 2 stack [])
                 < (λ time₁ msg₁ stack → acceptStateˢ time₁ msg₁ stack) >
HoareTripleStackGeAux' msg₁ pbk1 pbk2 pbk3 .==>stg time msg₂ (sig2 ∷ sig1 ∷ dummy ∷ s) (inj₁ (conj and3 and4))
          = boolToNatNotFalseLemma (compareSigsMultiSigAux msg₂ (sig2 ∷ []) (pbk2 ∷ pbk3 ∷ []) sig1
            (isSigned  msg₂ sig1 pbk1)) (lemmaHoareTripleStackGeAux'1 msg₂ pbk1 pbk2 pbk3 sig1 sig2 and3 and4)

HoareTripleStackGeAux' msg₁ pbk1 pbk2 pbk3 .==>stg time msg₂ (sig2 ∷ sig1 ∷ dummy ∷ s) (inj₂ (inj₁ (conj and3 and4)))
          = boolToNatNotFalseLemma (compareSigsMultiSigAux msg₂ (sig2 ∷ []) (pbk2 ∷ pbk3 ∷ []) sig1
             (isSigned  msg₂ sig1 pbk1)) (lemmaHoareTripleStackGeAux'2  msg₂ pbk1 pbk2 pbk3 sig1 sig2 and3 and4)

HoareTripleStackGeAux' msg₁ pbk1 pbk2 pbk3 .==>stg time msg₂ (sig2 ∷ sig1 ∷ dummy ∷ s) (inj₂ (inj₂ (conj and1 and2)))
          = boolToNatNotFalseLemma (compareSigsMultiSigAux msg₂ (sig2 ∷ []) (pbk2 ∷ pbk3 ∷ []) sig1
           (isSigned  msg₂ sig1 pbk1 )) (lemmaHoareTripleStackGeAux'3 msg₂ pbk1 pbk2 pbk3 sig1 sig2 and1 and2)

HoareTripleStackGeAux' msg₁ pbk1 pbk2 pbk3 {-numsig stack time₁-} .<==stg time msg₂ (sig2 ∷ sig1 ∷ dummy ∷ s) x
    = lemmaHoareTripleStackGeAux'4 msg₂ pbk1 pbk2 pbk3 sig1 sig2
        (boolToNatNotFalseLemma2 (compareSigsMultiSigAux msg₂ (sig2 ∷ []) (pbk2 ∷ pbk3 ∷ []) sig1
           (isSigned  msg₂ sig1 pbk1 )) x)


lemmaHoareTripleStackGeAux'7 : (msg₂ : Msg)
                               (pbk1 pbk2 pbk3 pbk4 sig1 sig2 : ℕ)
                               → True (isSigned  msg₂ sig1 pbk1)
                              →  True (isSigned  msg₂ sig2 pbk2)
                               → True (compareSigsMultiSig msg₂ ( sig1 ∷ sig2 ∷ []) (pbk1 ∷ pbk2 ∷ pbk3 ∷ pbk4 ∷  []))

lemmaHoareTripleStackGeAux'7 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ with  (isSigned  msg₂ sig1 pbk1)
lemmaHoareTripleStackGeAux'7 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true with (isSigned  msg₂ sig2 pbk2)
lemmaHoareTripleStackGeAux'7 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | true = tt


lemmaHoareTripleStackGeAux'8 : (msg₂ : Msg)
                               (pbk1 pbk2 pbk3 pbk4 sig1 sig2 : ℕ)
                               → True (isSigned  msg₂ sig1 pbk1)
                              →  True (isSigned  msg₂ sig2 pbk3)
                               → True (compareSigsMultiSig msg₂ ( sig1 ∷ sig2 ∷ []) (pbk1 ∷ pbk2 ∷ pbk3 ∷ pbk4 ∷  []))

lemmaHoareTripleStackGeAux'8 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ with  (isSigned  msg₂ sig2 pbk1)
lemmaHoareTripleStackGeAux'8 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | false with (isSigned  msg₂ sig1 pbk1)
lemmaHoareTripleStackGeAux'8 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | false | true with  (isSigned  msg₂ sig2 pbk2)
lemmaHoareTripleStackGeAux'8 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | false | true | false with (isSigned  msg₂ sig2 pbk3)
lemmaHoareTripleStackGeAux'8 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | false | true | false | true = tt
lemmaHoareTripleStackGeAux'8 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | false | true | true = tt
lemmaHoareTripleStackGeAux'8 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true  with (isSigned  msg₂ sig1 pbk1)
lemmaHoareTripleStackGeAux'8 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | true with  (isSigned  msg₂ sig2 pbk2)
lemmaHoareTripleStackGeAux'8 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | true | false with  (isSigned  msg₂ sig2 pbk3)
lemmaHoareTripleStackGeAux'8 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | true | false | true = tt
lemmaHoareTripleStackGeAux'8 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | true | true = tt


lemmaHoareTripleStackGeAux'9 : (msg₂ : Msg)
                               (pbk1 pbk2 pbk3 pbk4 sig1 sig2 : ℕ)
                               → True (isSigned  msg₂ sig1 pbk1)
                              →  True (isSigned  msg₂ sig2 pbk4)
                               → True (compareSigsMultiSig msg₂ ( sig1 ∷ sig2 ∷ []) (pbk1 ∷ pbk2 ∷ pbk3 ∷ pbk4 ∷  []))

lemmaHoareTripleStackGeAux'9 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ with  (isSigned  msg₂ sig1 pbk1)
lemmaHoareTripleStackGeAux'9 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true with  (isSigned  msg₂ sig2 pbk2)
lemmaHoareTripleStackGeAux'9 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | false with  (isSigned  msg₂ sig2 pbk3)
lemmaHoareTripleStackGeAux'9 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | false | false with  (isSigned  msg₂ sig2 pbk4)
lemmaHoareTripleStackGeAux'9 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | false | false | true = tt
lemmaHoareTripleStackGeAux'9 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | false | true = tt
lemmaHoareTripleStackGeAux'9 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | true = tt




lemmaHoareTripleStackGeAux'10 : (msg₂ : Msg)
                               (pbk1 pbk2 pbk3 pbk4 sig1 sig2 : ℕ)
                               → True (isSigned  msg₂ sig1 pbk2)
                              →  True (isSigned  msg₂ sig2 pbk3)
                               → True (compareSigsMultiSig msg₂ ( sig1 ∷ sig2 ∷ []) (pbk1 ∷ pbk2 ∷ pbk3 ∷ pbk4 ∷  []))

lemmaHoareTripleStackGeAux'10 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ with  (isSigned  msg₂ sig1 pbk1)
lemmaHoareTripleStackGeAux'10 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | false with (isSigned  msg₂ sig1 pbk2)
lemmaHoareTripleStackGeAux'10 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | false | true with (isSigned  msg₂ sig2 pbk3)
lemmaHoareTripleStackGeAux'10 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | false | true | true = tt
lemmaHoareTripleStackGeAux'10 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true with  (isSigned  msg₂ sig2 pbk2)
lemmaHoareTripleStackGeAux'10 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | false with (isSigned  msg₂ sig2 pbk3)
lemmaHoareTripleStackGeAux'10 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | false | true = tt
lemmaHoareTripleStackGeAux'10 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | true = tt


lemmaHoareTripleStackGeAux'11 : (msg₂ : Msg)
                               (pbk1 pbk2 pbk3 pbk4 sig1 sig2 : ℕ)
                               → True (isSigned  msg₂ sig1 pbk2)
                              →  True (isSigned  msg₂ sig2 pbk4)
                               → True (compareSigsMultiSig msg₂ ( sig1 ∷ sig2 ∷ []) (pbk1 ∷ pbk2 ∷ pbk3 ∷ pbk4 ∷  []))

lemmaHoareTripleStackGeAux'11 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ with  (isSigned  msg₂ sig1 pbk1)
lemmaHoareTripleStackGeAux'11 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | false with (isSigned  msg₂ sig1 pbk2)
lemmaHoareTripleStackGeAux'11 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | false | true with   (isSigned  msg₂ sig2 pbk3)
lemmaHoareTripleStackGeAux'11 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | false | true | false with  (isSigned  msg₂ sig2 pbk4)
lemmaHoareTripleStackGeAux'11 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | false | true | false | true = tt
lemmaHoareTripleStackGeAux'11 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | false | true | true = tt
lemmaHoareTripleStackGeAux'11 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true with (isSigned  msg₂ sig2 pbk2)
lemmaHoareTripleStackGeAux'11 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | false with (isSigned  msg₂ sig2 pbk3)
lemmaHoareTripleStackGeAux'11 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | false | false with (isSigned  msg₂ sig2 pbk4)
lemmaHoareTripleStackGeAux'11 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | false | false | true = tt
lemmaHoareTripleStackGeAux'11 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | false | true = tt
lemmaHoareTripleStackGeAux'11 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | true = tt

lemmaHoareTripleStackGeAux'12 : (msg₂ : Msg)
                               (pbk1 pbk2 pbk3 pbk4 sig1 sig2 : ℕ)
                               → True (isSigned  msg₂ sig1 pbk3)
                              →  True (isSigned  msg₂ sig2 pbk4)
                               → True (compareSigsMultiSig msg₂ ( sig1 ∷ sig2 ∷ []) (pbk1 ∷ pbk2 ∷ pbk3 ∷ pbk4 ∷  []))

lemmaHoareTripleStackGeAux'12 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ with  (isSigned  msg₂ sig1 pbk1)
lemmaHoareTripleStackGeAux'12 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | false with  (isSigned  msg₂ sig1 pbk2)
lemmaHoareTripleStackGeAux'12 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | false | false with  (isSigned  msg₂ sig1 pbk3)
lemmaHoareTripleStackGeAux'12 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | false | false | true with  (isSigned  msg₂ sig2 pbk4)
lemmaHoareTripleStackGeAux'12 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | false | false | true | true = tt
lemmaHoareTripleStackGeAux'12 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | false | true with (isSigned  msg₂ sig2 pbk3)
lemmaHoareTripleStackGeAux'12 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | false | true | false with  (isSigned  msg₂ sig2 pbk4)
lemmaHoareTripleStackGeAux'12 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | false | true | false | true = tt
lemmaHoareTripleStackGeAux'12 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | false | true | true = tt
lemmaHoareTripleStackGeAux'12 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true with  (isSigned  msg₂ sig2 pbk2)
lemmaHoareTripleStackGeAux'12 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | false with (isSigned  msg₂ sig2 pbk3)
lemmaHoareTripleStackGeAux'12 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | false | false with  (isSigned  msg₂ sig2 pbk4)
lemmaHoareTripleStackGeAux'12 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | false | false | true = tt
lemmaHoareTripleStackGeAux'12 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | false | true = tt
lemmaHoareTripleStackGeAux'12 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x x₁ | true | true = tt

lemmaHoareTripleStackGeAux'Comb2-4 : (msg₂ : Msg)
         (pbk1 pbk2 pbk3 pbk4 sig1 sig2 : ℕ)
          → True (compareSigsMultiSigAux msg₂ (sig2 ∷ []) (pbk2 ∷ pbk3 ∷  pbk4 ∷ [])  sig1
                 (isSigned  msg₂ sig1 pbk1 ))
          →  (True (isSigned  msg₂ sig1 pbk1) ∧ True (isSigned  msg₂ sig2 pbk2)) ⊎
             (True (isSigned  msg₂ sig1 pbk1) ∧ True (isSigned  msg₂ sig2 pbk3)) ⊎
             (True (isSigned  msg₂ sig1 pbk1) ∧ True (isSigned  msg₂ sig2 pbk4)) ⊎
             (True (isSigned  msg₂ sig1 pbk2) ∧ True (isSigned  msg₂ sig2 pbk3)) ⊎
             (True (isSigned  msg₂ sig1 pbk2) ∧ True (isSigned  msg₂ sig2 pbk4)) ⊎
             (True (isSigned  msg₂ sig1 pbk3) ∧ True (isSigned  msg₂ sig2 pbk4))
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x with (isSigned  msg₂ sig1 pbk1)
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | false with (isSigned  msg₂ sig1 pbk2)
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | false | false with (isSigned  msg₂ sig1 pbk3)
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | false | false | false with (isSigned  msg₂ sig1 pbk4)
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 () | false | false | false | false
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 () | false | false | false | true
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | false | false | true with (isSigned  msg₂ sig2 pbk4)
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 tt | false | false | true | true with  (isSigned  msg₂ sig2 pbk3)
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 tt | false | false | true | true | false with (isSigned  msg₂ sig2 pbk2)
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 tt | false | false | true | true | false | false = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (conj tt tt)))))
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 tt | false | false | true | true | false | true = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (conj tt tt)))))
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 tt | false | false | true | true | true with (isSigned  msg₂ sig2 pbk2)
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 tt | false | false | true | true | true | false = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (conj tt tt)))))
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 tt | false | false | true | true | true | true = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (conj tt tt)))))
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | false | true with (isSigned  msg₂ sig2 pbk3)
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | false | true | false with  (isSigned  msg₂ sig2 pbk4)
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | false | true | false | true with isSigned  msg₂ sig1 pbk3
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | false | true | false | true | false with (isSigned  msg₂ sig2 pbk2)
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | false | true | false | true | false | false = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (conj tt tt)))))
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | false | true | false | true | false | true = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (conj tt tt)))))
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | false | true | false | true | true with (isSigned  msg₂ sig2 pbk2)
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | false | true | false | true | true | false = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (conj tt tt)))))
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | false | true | false | true | true | true = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (conj tt tt)))))
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | false | true | true with (isSigned  msg₂ sig2 pbk4)
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | false | true | true | false with (isSigned  msg₂ sig1 pbk3)
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | false | true | true | false | false with (isSigned  msg₂ sig2 pbk2)
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | false | true | true | false | false | false = inj₂ (inj₂ (inj₂ (inj₁ (conj tt tt))))
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | false | true | true | false | false | true = inj₂ (inj₂ (inj₂ (inj₁ (conj tt tt))))
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | false | true | true | false | true = inj₂ (inj₂ (inj₂ (inj₁ (conj tt tt))))
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | false | true | true | true = inj₂ (inj₂ (inj₂ (inj₁ (conj tt tt))))
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | true with (isSigned  msg₂ sig2 pbk2)
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | true | false with (isSigned  msg₂ sig2 pbk3)
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | true | false | false with (isSigned  msg₂ sig2 pbk4)
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | true | false | false | true = inj₂ (inj₂ (inj₁ (conj tt tt)))
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | true | false | true = inj₂ (inj₁ (conj tt tt))
lemmaHoareTripleStackGeAux'Comb2-4 msg₂ pbk1 pbk2 pbk3 pbk4 sig1 sig2 x | true | true = inj₁ (conj tt tt)





lemmaHoareTripleStackGeAux'14 : (msg : Msg)
                               (pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 : ℕ)
                              → True (isSigned  msg sig1 pbk1)
                              → True (isSigned  msg sig3 pbk3)
                              → True (isSigned  msg sig2 pbk2)
                              → True (compareSigsMultiSig msg ( sig1 ∷ sig2 ∷ sig3 ∷ []) (pbk1 ∷ pbk2 ∷ pbk3 ∷ pbk4 ∷ pbk5 ∷ []))
lemmaHoareTripleStackGeAux'14 msg pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ with (isSigned  msg sig1 pbk1)
lemmaHoareTripleStackGeAux'14 msg pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true  with (isSigned  msg sig2 pbk2)
lemmaHoareTripleStackGeAux'14 msg pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true with (isSigned  msg sig3 pbk3)
lemmaHoareTripleStackGeAux'14 msg pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | true = tt


lemmaHoareTripleStackGeAux'15 : (msg : Msg)
                               (pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 : ℕ)
                               → True (isSigned  msg sig3 pbk4)
                              →  True (isSigned  msg sig2 pbk2)
                              →  True (isSigned  msg sig1 pbk1)
                               → True (compareSigsMultiSig msg ( sig1 ∷ sig2 ∷ sig3 ∷ []) (pbk1 ∷ pbk2 ∷ pbk3 ∷ pbk4 ∷ pbk5 ∷ []))
lemmaHoareTripleStackGeAux'15 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ with (isSigned  msg₁ sig1 pbk1)
lemmaHoareTripleStackGeAux'15 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true with (isSigned  msg₁ sig2 pbk2)
lemmaHoareTripleStackGeAux'15 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true with (isSigned  msg₁ sig3 pbk3)
lemmaHoareTripleStackGeAux'15 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false with  (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'15 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false | true = tt
lemmaHoareTripleStackGeAux'15 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | true = tt


lemmaHoareTripleStackGeAux'16 : (msg : Msg)
                               (pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 : ℕ)
                               → True (isSigned  msg sig3 pbk5)
                              →  True (isSigned  msg sig2 pbk2)
                               →  True (isSigned  msg sig1 pbk1)
                               → True (compareSigsMultiSig msg ( sig1 ∷ sig2 ∷ sig3 ∷ []) (pbk1 ∷ pbk2 ∷ pbk3 ∷ pbk4 ∷ pbk5 ∷ []))
lemmaHoareTripleStackGeAux'16 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ with (isSigned  msg₁ sig1 pbk1)
lemmaHoareTripleStackGeAux'16 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true with (isSigned  msg₁ sig2 pbk2)
lemmaHoareTripleStackGeAux'16 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true with  (isSigned  msg₁ sig3 pbk3)
lemmaHoareTripleStackGeAux'16 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false with  (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'16 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false | false with (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'16 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false | false | true = tt
lemmaHoareTripleStackGeAux'16 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false | true = tt
lemmaHoareTripleStackGeAux'16 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | true = tt


lemmaHoareTripleStackGeAux'17 : (msg : Msg)
                               (pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 : ℕ)
                               → True (isSigned  msg sig3 pbk4)
                              →  True (isSigned  msg sig2 pbk3)
                               →  True (isSigned  msg sig1 pbk1)
                               → True (compareSigsMultiSig msg ( sig1 ∷ sig2 ∷ sig3 ∷ []) (pbk1 ∷ pbk2 ∷ pbk3 ∷ pbk4 ∷ pbk5 ∷ []))
lemmaHoareTripleStackGeAux'17 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ with (isSigned  msg₁ sig1 pbk1)
lemmaHoareTripleStackGeAux'17 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true with  (isSigned  msg₁ sig2 pbk2)
lemmaHoareTripleStackGeAux'17 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false with (isSigned  msg₁ sig2 pbk3)
lemmaHoareTripleStackGeAux'17 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true with  (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'17 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true | true = tt
lemmaHoareTripleStackGeAux'17 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true with (isSigned  msg₁ sig3 pbk3)
lemmaHoareTripleStackGeAux'17 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false with  (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'17 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false | true = tt
lemmaHoareTripleStackGeAux'17 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | true = tt


lemmaHoareTripleStackGeAux'18 : (msg : Msg)
                               (pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 : ℕ)
                               → True (isSigned  msg sig3 pbk5)
                              →  True (isSigned  msg sig2 pbk3)
                              →  True (isSigned  msg sig1 pbk1)
                               → True (compareSigsMultiSig msg ( sig1 ∷ sig2 ∷ sig3 ∷ []) (pbk1 ∷ pbk2 ∷ pbk3 ∷ pbk4 ∷ pbk5 ∷ []))
lemmaHoareTripleStackGeAux'18 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ with (isSigned  msg₁ sig1 pbk1)
lemmaHoareTripleStackGeAux'18 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true with (isSigned  msg₁ sig2 pbk2)
lemmaHoareTripleStackGeAux'18 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false with  (isSigned  msg₁ sig2 pbk3)
lemmaHoareTripleStackGeAux'18 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true with (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'18 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true | false with (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'18 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true | false | true = tt
lemmaHoareTripleStackGeAux'18 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true | true = tt
lemmaHoareTripleStackGeAux'18 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true with (isSigned  msg₁ sig3 pbk3)
lemmaHoareTripleStackGeAux'18 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false with (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'18 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false | false with (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'18 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false | false | true = tt
lemmaHoareTripleStackGeAux'18 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false | true = tt
lemmaHoareTripleStackGeAux'18 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | true = tt


lemmaHoareTripleStackGeAux'19 : (msg : Msg)
                               (pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 : ℕ)
                               → True (isSigned  msg sig3 pbk5)
                              →  True (isSigned  msg sig2 pbk4)
                               →  True (isSigned  msg sig1 pbk1)
                               → True (compareSigsMultiSig msg ( sig1 ∷ sig2 ∷ sig3 ∷ []) (pbk1 ∷ pbk2 ∷ pbk3 ∷ pbk4 ∷ pbk5 ∷ []))
lemmaHoareTripleStackGeAux'19 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ with  (isSigned  msg₁ sig1 pbk1)
lemmaHoareTripleStackGeAux'19 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true with (isSigned  msg₁ sig2 pbk2)
lemmaHoareTripleStackGeAux'19 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false with  (isSigned  msg₁ sig2 pbk3)
lemmaHoareTripleStackGeAux'19 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | false with (isSigned  msg₁ sig2 pbk4)
lemmaHoareTripleStackGeAux'19 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | false | true with  (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'19 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | false | true | true = tt
lemmaHoareTripleStackGeAux'19 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true with (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'19 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true | false with   (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'19 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true | false | true = tt
lemmaHoareTripleStackGeAux'19 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true | true = tt
lemmaHoareTripleStackGeAux'19 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true with (isSigned  msg₁ sig3 pbk3)
lemmaHoareTripleStackGeAux'19 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false with (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'19 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false | false with  (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'19 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false | false | true = tt
lemmaHoareTripleStackGeAux'19 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false | true = tt
lemmaHoareTripleStackGeAux'19 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | true = tt

lemmaHoareTripleStackGeAux'20 : (msg : Msg)
                               (pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 : ℕ)
                               → True (isSigned  msg sig3 pbk4)
                              →  True (isSigned  msg sig2 pbk3)
                              →  True (isSigned  msg sig1 pbk2)
                               → True (compareSigsMultiSig msg ( sig1 ∷ sig2 ∷ sig3 ∷ []) (pbk1 ∷ pbk2 ∷ pbk3 ∷ pbk4 ∷ pbk5 ∷ []))
lemmaHoareTripleStackGeAux'20 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ with (isSigned  msg₁ sig1 pbk1)
lemmaHoareTripleStackGeAux'20 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false with (isSigned  msg₁ sig1 pbk2)
lemmaHoareTripleStackGeAux'20 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true with  (isSigned  msg₁ sig2 pbk3)
lemmaHoareTripleStackGeAux'20 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true | true with (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'20 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true | true | true = tt
lemmaHoareTripleStackGeAux'20 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true with (isSigned  msg₁ sig2 pbk2)
lemmaHoareTripleStackGeAux'20 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false with (isSigned  msg₁ sig2 pbk3)
lemmaHoareTripleStackGeAux'20 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true with (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'20 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true | true = tt
lemmaHoareTripleStackGeAux'20 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true with (isSigned  msg₁ sig3 pbk3)
lemmaHoareTripleStackGeAux'20 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false with (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'20 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false | true = tt
lemmaHoareTripleStackGeAux'20 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | true = tt



lemmaHoareTripleStackGeAux'21 : (msg : Msg)
                               (pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 : ℕ)
                               → True (isSigned  msg sig3 pbk5)
                              →  True (isSigned  msg sig2 pbk3)
                              →  True (isSigned  msg sig1 pbk2)
                               → True (compareSigsMultiSig msg ( sig1 ∷ sig2 ∷ sig3 ∷ []) (pbk1 ∷ pbk2 ∷ pbk3 ∷ pbk4 ∷ pbk5 ∷ []))
lemmaHoareTripleStackGeAux'21 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ with (isSigned  msg₁ sig1 pbk1)
lemmaHoareTripleStackGeAux'21 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false with (isSigned  msg₁ sig1 pbk2)
lemmaHoareTripleStackGeAux'21 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true with (isSigned  msg₁ sig2 pbk3)
lemmaHoareTripleStackGeAux'21 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true | true with  (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'21 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true | true | false with  (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'21 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true | true | false | true = tt
lemmaHoareTripleStackGeAux'21 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true | true | true = tt
lemmaHoareTripleStackGeAux'21 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true with  (isSigned  msg₁ sig2 pbk2)
lemmaHoareTripleStackGeAux'21 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false with (isSigned  msg₁ sig2 pbk3)
lemmaHoareTripleStackGeAux'21 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true with (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'21 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true | false with (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'21 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true | false | true = tt
lemmaHoareTripleStackGeAux'21 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true | true = tt
lemmaHoareTripleStackGeAux'21 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true with (isSigned  msg₁ sig3 pbk3)
lemmaHoareTripleStackGeAux'21 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false with (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'21 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false | false with (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'21 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false | false | true = tt
lemmaHoareTripleStackGeAux'21 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false | true = tt
lemmaHoareTripleStackGeAux'21 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | true = tt





lemmaHoareTripleStackGeAux'22 : (msg : Msg)
                               (pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 : ℕ)
                               → True (isSigned  msg sig3 pbk5)
                              →  True (isSigned  msg sig2 pbk4)
                              →  True (isSigned  msg sig1 pbk2)
                               → True (compareSigsMultiSig msg ( sig1 ∷ sig2 ∷ sig3 ∷ []) (pbk1 ∷ pbk2 ∷ pbk3 ∷ pbk4 ∷ pbk5 ∷ []))
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ with (isSigned  msg₁ sig1 pbk1)
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false with  (isSigned  msg₁ sig1 pbk2)
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true with (isSigned  msg₁ sig2 pbk3)
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true | false with  (isSigned  msg₁ sig2 pbk4)
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true | false | true with (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true | false | true | true = tt
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true | true with (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true | true | false with (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true | true | false | true = tt
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true | true | true = tt
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true with (isSigned  msg₁ sig2 pbk2)
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false with  (isSigned  msg₁ sig2 pbk3)
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | false with (isSigned  msg₁ sig2 pbk4)
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | false | true with  (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | false | true | true = tt
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true with (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true | false with  (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true | false | true = tt
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true | true = tt
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true with (isSigned  msg₁ sig3 pbk3)
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false with (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false | false with  (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false | false | true = tt
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false | true = tt
lemmaHoareTripleStackGeAux'22 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | true = tt



lemmaHoareTripleStackGeAux'23 : (msg : Msg)
                               (pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 : ℕ)
                               → True (isSigned  msg sig3 pbk5)
                              →  True (isSigned  msg sig2 pbk4)
                              →  True (isSigned  msg sig1 pbk3)
                               → True (compareSigsMultiSig msg ( sig1 ∷ sig2 ∷ sig3 ∷ []) (pbk1 ∷ pbk2 ∷ pbk3 ∷ pbk4 ∷ pbk5 ∷ []))
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ with (isSigned  msg₁ sig1 pbk1)
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false with (isSigned  msg₁ sig1 pbk2)
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | false with (isSigned  msg₁ sig1 pbk3)
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | false | true with (isSigned  msg₁ sig2 pbk4)
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | false | true | true with (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | false | true | true | true = tt
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true with (isSigned  msg₁ sig2 pbk3)
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true | false with (isSigned  msg₁ sig2 pbk4)
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true | false | true with (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true | false | true | true = tt
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true | true with (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true | true | false with (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true | true | false | true = tt
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | false | true | true | true = tt
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true with (isSigned  msg₁ sig2 pbk2)
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false with (isSigned  msg₁ sig2 pbk3)
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | false with (isSigned  msg₁ sig2 pbk4)
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | false | true with  (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | false | true | true = tt
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true with (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true | false with  (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true | false | true = tt
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | false | true | true = tt
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true with (isSigned  msg₁ sig3 pbk3)
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false with (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false | false with (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false | false | true = tt
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | false | true = tt
lemmaHoareTripleStackGeAux'23 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x x₁ x₂ | true | true | true = tt





lemmaHoareTripleStackGeAux'Comb3-5 : (msg₁ : Msg)
         (pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 : ℕ)
          → True (compareSigsMultiSigAux msg₁ (sig2 ∷ sig3 ∷ []) ( pbk2 ∷ pbk3 ∷ pbk4 ∷ pbk5 ∷ [])  sig1
                 (isSigned  msg₁ sig1 pbk1 ))
      →  ((True (isSigned  msg₁ sig1 pbk1) ∧ True (isSigned  msg₁ sig2 pbk2)) ∧ True (isSigned  msg₁ sig3 pbk3)) ⊎
          ((True (isSigned  msg₁ sig1 pbk1) ∧ True (isSigned  msg₁ sig2 pbk2)) ∧ True (isSigned  msg₁ sig3 pbk4)) ⊎
          ((True (isSigned  msg₁ sig1 pbk1) ∧ True (isSigned  msg₁ sig2 pbk2)) ∧ True (isSigned  msg₁ sig3 pbk5)) ⊎
          ((True (isSigned  msg₁ sig1 pbk1) ∧ True (isSigned  msg₁ sig2 pbk3)) ∧ True (isSigned  msg₁ sig3 pbk4)) ⊎
          ((True (isSigned  msg₁ sig1 pbk1) ∧ True (isSigned  msg₁ sig2 pbk3)) ∧ True (isSigned  msg₁ sig3 pbk5)) ⊎
          ((True (isSigned  msg₁ sig1 pbk1) ∧ True (isSigned  msg₁ sig2 pbk4)) ∧ True (isSigned  msg₁ sig3 pbk5)) ⊎
          ((True (isSigned  msg₁ sig1 pbk2) ∧ True (isSigned  msg₁ sig2 pbk3)) ∧ True (isSigned  msg₁ sig3 pbk4)) ⊎
          ((True (isSigned  msg₁ sig1 pbk2) ∧ True (isSigned  msg₁ sig2 pbk3)) ∧ True (isSigned  msg₁ sig3 pbk5)) ⊎
          ((True (isSigned  msg₁ sig1 pbk2) ∧ True (isSigned  msg₁ sig2 pbk4)) ∧ True (isSigned  msg₁ sig3 pbk5)) ⊎
          ((True (isSigned  msg₁ sig1 pbk3) ∧ True (isSigned  msg₁ sig2 pbk4)) ∧ True (isSigned  msg₁ sig3 pbk5))

lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x with  (isSigned  msg₁ sig1 pbk1)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | false with (isSigned  msg₁ sig1 pbk2)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | false | false with (isSigned  msg₁ sig1 pbk3)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | false | false | false with (isSigned  msg₁ sig1 pbk4)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | false | false | false | false with (isSigned  msg₁ sig1 pbk5)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 () | false | false | false | false | false
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 () | false | false | false | false | true
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | false | false | false | true with  (isSigned  msg₁ sig2 pbk5)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 () | false | false | false | true | false
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 () | false | false | false | true | true
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | false | false | true with  (isSigned  msg₁ sig2 pbk4)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | false | false | true | false with (isSigned  msg₁ sig2 pbk5)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 () | false | false | true | false | false
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 () | false | false | true | false | true
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | false | false | true | true with  (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | false | false | true | true | true
                                                              = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (conj (conj tt tt) tt)))))))))
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | false | true with (isSigned  msg₁ sig2 pbk3)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | false | true | false with  (isSigned  msg₁ sig2 pbk4)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | false | true | false | false with (isSigned  msg₁ sig2 pbk5)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 () | false | true | false | false | false
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 () | false | true | false | false | true
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | false | true | false | true with (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | false | true | false | true | true
                                                        =  inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (conj (conj tt tt) tt)))))))))
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | false | true | true with (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | false | true | true | false with (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | false | true | true | false | true
                                                        = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (conj (conj tt tt) tt))))))))
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | false | true | true | true
                                                        = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (conj (conj tt tt) tt)))))))
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | true with (isSigned  msg₁ sig2 pbk2)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | true | false with (isSigned  msg₁ sig2 pbk3)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | true | false | false with  (isSigned  msg₁ sig2 pbk4)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | true | false | false | false with  (isSigned  msg₁ sig2 pbk5)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 () | true | false | false | false | false
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 () | true | false | false | false | true
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | true | false | false | true with  (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | true | false | false | true | true
                                                        = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (conj (conj tt tt) tt))))))
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | true | false | true with  (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | true | false | true | false with  (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | true | false | true | false | true
                                                        = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (conj (conj tt tt) tt)))))
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | true | false | true | true
                                                        = inj₂ (inj₂ (inj₂ (inj₁ (conj (conj tt tt) tt))))
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | true | true with  (isSigned  msg₁ sig3 pbk3)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | true | true | false with (isSigned  msg₁ sig3 pbk4)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | true | true | false | false with (isSigned  msg₁ sig3 pbk5)
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | true | true | false | false | true
                                                        = inj₂ (inj₂ (inj₁ (conj (conj tt tt) tt)))
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | true | true | false | true = inj₂ (inj₁ (conj (conj tt tt) tt))
lemmaHoareTripleStackGeAux'Comb3-5 msg₁ pbk1 pbk2 pbk3 pbk4 pbk5 sig1 sig2 sig3 x | true | true | true = inj₁ (conj (conj tt tt) tt)


--complex multisig
multiSigScript2-4ᵇ : (pbk₁ pbk₂ pbk₃ pbk₄ :  ℕ) → BitcoinScriptBasic
multiSigScript2-4ᵇ  pbk₁ pbk₂ pbk₃ pbk₄ =  (opPush 2) ∷ (opPush pbk₁) ∷  (opPush pbk₂) ∷
                    (opPush pbk₃) ∷  (opPush pbk₄) ∷ (opPush 4) ∷  [  opMultiSig ]


multiSigScript-3-5-b : (pbk1 pbk2 pbk3 pbk4 pbk5 :  ℕ) → BitcoinScriptBasic
multiSigScript-3-5-b pbk1 pbk2 pbk3 pbk4 pbk5 =
      (opPush 3) ∷ (opPush pbk1) ∷  (opPush pbk2) ∷  (opPush pbk3) ∷  (opPush pbk4) ∷  (opPush pbk5) ∷ (opPush 5) ∷ opMultiSig ∷ []

--multisig check Time Script

checkTimeScriptᵇ : (time₁ : Time) → BitcoinScriptBasic
checkTimeScriptᵇ time₁ = (opPush time₁) ∷ opCHECKLOCKTIMEVERIFY ∷ [ opDrop  ]








{- Next steps -}



--new

lemmaHoareTripleStackGeAux'5 : (msg : Msg)
                               (pbk1 pbk2 pbk3 sig1 sig3 : ℕ)
                               → True (isSigned  msg sig1 pbk1)
                              →  True (isSigned  msg sig3 pbk3)
                               → True (compareSigsMultiSig msg ( sig1 ∷ sig3 ∷ []) (pbk1 ∷ pbk2 ∷ pbk3 ∷ []))
lemmaHoareTripleStackGeAux'5 msg pbk1 pbk2 pbk3 sig1 sig3 x x₁  with (isSigned  msg sig1 pbk1)
lemmaHoareTripleStackGeAux'5 msg pbk1 pbk2 pbk3 sig1 sig3 x x₁ | true with (isSigned  msg sig3 pbk2)
lemmaHoareTripleStackGeAux'5 msg pbk1 pbk2 pbk3 sig1 sig3 x x₁ | true | false with (isSigned  msg sig3 pbk3)
lemmaHoareTripleStackGeAux'5 msg pbk1 pbk2 pbk3 sig1 sig3 x x₁ | true | false | true = tt
lemmaHoareTripleStackGeAux'5 msg pbk1 pbk2 pbk3 sig1 sig3 x x₁ | true | true = tt







--multisig time Check PreCond
timeCheckPreCond : (time₁ : Time) → StackPredicate
timeCheckPreCond time₁ time₂ msg stack₁ = time₁ ≤ time₂

