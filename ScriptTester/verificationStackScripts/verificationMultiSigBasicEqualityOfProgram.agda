{-# OPTIONS --allow-unsolved-metas #-}

open import basicBitcoinDataType

module verificationStackScripts.verificationMultiSigBasicEqualityOfProgram (param : GlobalParameters) where


open import Data.List.Base hiding (_++_ )
open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_  )
open import Data.Sum
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Maybe
open import Data.Bool  hiding (_≤_ ; _<_ ; if_then_else_  )  renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_ ; _<_)
open import Data.List.NonEmpty hiding (head; [_])
open import Data.Nat using (ℕ; _+_; _≥_; _>_; zero; suc; s≤s; z≤n)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality


--our libraries
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
open import semanticBasicOperations param
open import instructionBasic
open import verificationMultiSig param
open import verificationStackScripts.semanticsStackInstructions param
open import verificationStackScripts.stackVerificationLemmas param
open import verificationStackScripts.stackHoareTriple param
open import verificationStackScripts.sPredicate
open import verificationStackScripts.hoareTripleStackBasic param
open import verificationStackScripts.stackState
open import verificationStackScripts.stackSemanticsInstructionsBasic param
open import verificationStackScripts.verificationMultiSigBasic param

-----------------------------------------------------------------
--   the main part of symbolic execution has been moved to
--   verificationMultiSigBasicSymbolicExecution.agda
--
--   There we dig out how the nested case distinction operates
--     and we can see directly that the weakest pre condition is
--     what we used in verificationMultiSigBasic.agda
--     for verifying the program
--
--
--
--  The following is not really necessary for the verifiation
--   namely to prove that the program is equivalent to a
--   program which follows this case distinction.
--  It is not necessary since it is easier to prove the conditions directly
--    then using this tedious prove of giving an equivalent definition
------------------------------------------------------------------------------

{- there are still some open goals in the following -}

extractedFunctionPMSauxStep1FalseStep2FalseStep3FalseStep4 : (b : Bool) → Bool
extractedFunctionPMSauxStep1FalseStep2FalseStep3FalseStep4 true = false
extractedFunctionPMSauxStep1FalseStep2FalseStep3FalseStep4 false = false


extractedFunctionPMSauxStep1FalseStep2FalseStep3TrueStep4 : (b : Bool) → Bool
extractedFunctionPMSauxStep1FalseStep2FalseStep3TrueStep4 true = true
extractedFunctionPMSauxStep1FalseStep2FalseStep3TrueStep4 false = false

-- should be equal to
-- compareSigsMultiSigAux msg₁ (sig1 ∷ []) (pbk₄ ∷ []) sig2 (param .signed msg₁ sig2 pbk₃)
extractedFunctionPMSauxStep1FalseStep2FalseStep3 : (pbk₄ : ℕ)(msg₁ : Msg)(sig₁ sig₂ : ℕ)(b : Bool) → Bool
extractedFunctionPMSauxStep1FalseStep2FalseStep3 pbk₄ msg₁ sig₁ sig₂ true = extractedFunctionPMSauxStep1FalseStep2FalseStep3TrueStep4 (param .signed msg₁ sig₁ pbk₄)
extractedFunctionPMSauxStep1FalseStep2FalseStep3 pbk₄ msg₁ sig₁ sig₂ false = extractedFunctionPMSauxStep1FalseStep2FalseStep3FalseStep4 (param .signed msg₁ sig₂ pbk₄)


-- should be equal to
-- compareSigsMultiSigAux msg₁ [] [] sig1 (param .signed msg₁ sig1 pbk₄)
extractedFunctionPMSauxStep1FalseStep2TrueStep3FalseStep4 : (b : Bool) → Bool
extractedFunctionPMSauxStep1FalseStep2TrueStep3FalseStep4 false = false
extractedFunctionPMSauxStep1FalseStep2TrueStep3FalseStep4 true = true

-- should be equal to
-- compareSigsMultiSigAux msg₁ [] (pbk₄ ∷ []) sig1 (param .signed msg₁ sig1 pbk₃)
extractedFunctionPMSauxStep1FalseStep2TrueStep3 : (pbk₄ : ℕ)(msg₁ : Msg)(sig₁ : ℕ)(b : Bool) → Bool
extractedFunctionPMSauxStep1FalseStep2TrueStep3 pbk₄ msg₁ sig₁ true = true
extractedFunctionPMSauxStep1FalseStep2TrueStep3 pbk₄ msg₁ sig₁ false = extractedFunctionPMSauxStep1FalseStep2TrueStep3FalseStep4 (param .signed msg₁ sig₁ pbk₄)

-- should be equal to
-- compareSigsMultiSigAux msg₁ (sig1 ∷ []) (pbk₃ ∷ pbk₄ ∷ []) sig2 (param .signed msg₁ sig2 pbk₂)
extractedFunctionPMSauxStep1FalseStep2 : (pbk₃ pbk₄ : ℕ)(msg₁ : Msg)(sig₁ sig₂ : ℕ)(b : Bool) → Bool
extractedFunctionPMSauxStep1FalseStep2 pbk₃ pbk₄ msg₁ sig₁ sig₂ true = extractedFunctionPMSauxStep1FalseStep2TrueStep3 pbk₄ msg₁ sig₁ (param .signed msg₁ sig₁ pbk₃)
extractedFunctionPMSauxStep1FalseStep2 pbk₃ pbk₄ msg₁ sig₁ sig₂ false = extractedFunctionPMSauxStep1FalseStep2FalseStep3 pbk₄ msg₁ sig₁ sig₂ (param .signed msg₁ sig₂ pbk₃)


-- should be equal to
-- compareSigsMultiSigAux msg₁ [] [] sig1 (param .signed msg₁ sig1 pbk₄)
extractedFunctionPMSauxStep1TrueStep2FalseStep3FalseStep4 : (b : Bool) → Bool
extractedFunctionPMSauxStep1TrueStep2FalseStep3FalseStep4 true = true
extractedFunctionPMSauxStep1TrueStep2FalseStep3FalseStep4 false = false


-- should be equal to
-- compareSigsMultiSigAux msg₁ [] (pbk₄ ∷ []) sig1 (param .signed msg₁ sig1 pbk₃)
extractedFunctionPMSauxStep1TrueStep2FalseStep3 : (pbk₄ : ℕ)(msg₁ : Msg)(sig₁ : ℕ)(b : Bool) → Bool
extractedFunctionPMSauxStep1TrueStep2FalseStep3 pbk₄ msg₁ sig₁ true = true -- extractedFunctionPMSauxStep1TrueStep2FalseStep3FalseStep4 (param .signed msg₁ sig₁ pbk₄)
extractedFunctionPMSauxStep1TrueStep2FalseStep3 pbk₄ msg₁ sig₁ false = extractedFunctionPMSauxStep1TrueStep2FalseStep3FalseStep4 (param .signed msg₁ sig₁ pbk₄)


-- should be equal to
-- compareSigsMultiSigAux msg₁ [] (pbk₃ ∷ pbk₄ ∷ []) sig1 (param .signed msg₁ sig1 pbk₂)
extractedFunctionPMSauxStep1TrueStep2 : (pbk₃ pbk₄ : ℕ)(msg₁ : Msg)(sig₁ : ℕ)(b : Bool) → Bool
extractedFunctionPMSauxStep1TrueStep2 pbk₃ pbk₄ msg₁ sig₁ true = true
extractedFunctionPMSauxStep1TrueStep2 pbk₃ pbk₄ msg₁ sig₁ false = extractedFunctionPMSauxStep1TrueStep2FalseStep3 pbk₄ msg₁ sig₁ (param .signed msg₁ sig₁ pbk₃)


-- should be equal to
-- compareSigsMultiSigAux msg₁ (sig1 ∷ []) (pbk₂ ∷ pbk₃ ∷ pbk₄ ∷ []) sig2  (param .signed msg₁ sig2 pbk₁)
extractedFunctionPMSauxStep1 : (pbk₂ pbk₃ pbk₄ : ℕ)(msg₁ : Msg)(sig₁ sig₂ : ℕ)(b : Bool) → Bool
extractedFunctionPMSauxStep1 pbk₂ pbk₃ pbk₄ msg₁ sig₁ sig₂ true = extractedFunctionPMSauxStep1TrueStep2 pbk₃ pbk₄ msg₁ sig₂ (param .signed msg₁ sig₂ pbk₂)
extractedFunctionPMSauxStep1 pbk₂ pbk₃ pbk₄ msg₁ sig₁ sig₂ false = extractedFunctionPMSauxStep1FalseStep2 pbk₃ pbk₄ msg₁ sig₁ sig₂ (param .signed msg₁ sig₂ pbk₂)


extractedFunctionPMSaux1 : (pbk₁ pbk₂ pbk₃ pbk₄ : ℕ)(msg₁ : Msg)(sig₁ sig₂ : ℕ) → Bool
extractedFunctionPMSaux1 pbk₁ pbk₂ pbk₃ pbk₄ msg₁ sig₁ sig₂  = extractedFunctionPMSauxStep1 pbk₂ pbk₃ pbk₄ msg₁ sig₁ sig₂ (param .signed msg₁ sig₂ pbk₁)

extractedFunctionPMS : (pbk₁ pbk₂ pbk₃ pbk₄ : ℕ)(msg₁ : Msg)(stack₁ : Stack) → Maybe Stack
extractedFunctionPMS pbk₁ pbk₂ pbk₃ pbk₄ msg₁ [] = nothing
extractedFunctionPMS pbk₁ pbk₂ pbk₃ pbk₄ msg₁ (n ∷ []) = nothing
extractedFunctionPMS pbk₁ pbk₂ pbk₃ pbk₄ msg₁ (n₁ ∷ n₂  ∷ []) = nothing
extractedFunctionPMS pbk₁ pbk₂ pbk₃ pbk₄ msg₁ (sig₁ ∷ sig₂ ∷ dummy ∷ stack₁) =
              just (boolToNat(extractedFunctionPMSaux1 pbk₁ pbk₂ pbk₃ pbk₄ msg₁  sig₁ sig₂) ∷ stack₁)



lemmaCorr1 : (pbk₁ pbk₂ pbk₃ pbk₄ : ℕ)(time₁ : Time)(msg₁ : Msg)
       → ⟦ multiSigScript-2-4-b pbk₁ pbk₂ pbk₃ pbk₄ ⟧stb time₁ msg₁ [] ≡  nothing
lemmaCorr1 pbk₁ pbk₂ pbk₃ pbk₄ time₁ msg₁ = refl

lemmaCorr2 : (pbk₁ pbk₂ pbk₃ pbk₄ : ℕ)(time₁ : Time)(msg₁ : Msg)(n : ℕ) (stack₁ : Stack)
       → ⟦ multiSigScript-2-4-b pbk₁ pbk₂ pbk₃ pbk₄ ⟧stb time₁ msg₁ (n ∷ []) ≡  nothing
lemmaCorr2 pbk₁ pbk₂ pbk₃ pbk₄ time₁ msg₁ stack₁ n  = refl

lemmaCorr3 : (pbk₁ pbk₂ pbk₃ pbk₄ : ℕ)(time₁ : Time)(msg₁ : Msg)(n₁ n₂ : ℕ) (stack₁ : Stack)
       → ⟦ multiSigScript-2-4-b pbk₁ pbk₂ pbk₃ pbk₄ ⟧stb time₁ msg₁ (n₁ ∷ n₂  ∷ []) ≡  nothing
lemmaCorr3 pbk₁ pbk₂ pbk₃ pbk₄ time₁ msg₁ stack₁ n₁ n₂  = refl


lemmaCorr4 : (pbk₁ pbk₂ pbk₃ pbk₄ : ℕ)(time₁ : Time)(msg₁ : Msg)(stack₁ : Stack)(sig₁ sig₂ dummy : ℕ)
        → ⟦ multiSigScript-2-4-b pbk₁ pbk₂ pbk₃ pbk₄ ⟧stb time₁ msg₁ (sig₁ ∷ sig₂ ∷ dummy ∷ stack₁)
           ≡ just ( (boolToNat (compareSigsMultiSigAux msg₁ (sig₁ ∷ []) (pbk₂ ∷ pbk₃ ∷ pbk₄ ∷ [])
                                                             sig₂ (param .signed msg₁ sig₂ pbk₁))) ∷ stack₁)
lemmaCorr4 pbk₁ pbk₂ pbk₃ pbk₄ time₁ msg₁ stack₁ sig₁ sig₂ dummy  = refl

lemmaExtractedFunctionPMSauxStep1FalseStep2FalseStep3FalseStep4 : (msg₁ : Msg)(sig₁ sig₂ : ℕ)(b : Bool)
        → compareSigsMultiSigAux msg₁ (sig₁ ∷ []) [] sig₂ b ≡
           extractedFunctionPMSauxStep1FalseStep2FalseStep3FalseStep4 b
lemmaExtractedFunctionPMSauxStep1FalseStep2FalseStep3FalseStep4 msg₁ sig₁ sig₂ false = refl
lemmaExtractedFunctionPMSauxStep1FalseStep2FalseStep3FalseStep4 msg₁ sig₁ sig₂ true = refl


lemmaExtractedFunctionPMSauxStep1FalseStep2FalseStep3TrueStep4 : (msg₁ : Msg)(sig₁ : ℕ)(b : Bool)
           → compareSigsMultiSigAux msg₁ [] [] sig₁ b ≡
              extractedFunctionPMSauxStep1FalseStep2FalseStep3TrueStep4 b
lemmaExtractedFunctionPMSauxStep1FalseStep2FalseStep3TrueStep4 msg₁ sig₁ true = refl
lemmaExtractedFunctionPMSauxStep1FalseStep2FalseStep3TrueStep4  msg₁ sig₁ false = refl


lemmaExtractedFunctionPMSauxStep1FalseStep2FalseStep3 : (pbk₄ : ℕ)(msg₁ : Msg)(sig₁ sig₂ : ℕ)(b : Bool)
             → compareSigsMultiSigAux msg₁ (sig₁ ∷ []) (pbk₄ ∷ []) sig₂ b ≡
                extractedFunctionPMSauxStep1FalseStep2FalseStep3 pbk₄ msg₁ sig₁ sig₂ b
lemmaExtractedFunctionPMSauxStep1FalseStep2FalseStep3 pbk₄ msg₁ sig₁ sig₂ false = lemmaExtractedFunctionPMSauxStep1FalseStep2FalseStep3FalseStep4
                                                                                    msg₁ sig₁ sig₂ (param .signed msg₁ sig₂ pbk₄)
lemmaExtractedFunctionPMSauxStep1FalseStep2FalseStep3 pbk₄ msg₁ sig₁ sig₂ true = lemmaExtractedFunctionPMSauxStep1FalseStep2FalseStep3TrueStep4 msg₁
                                                                                   sig₁ (param .signed msg₁ sig₁ pbk₄)

lemmaExtractedFunctionPMSauxStep1FalseStep2TrueStep3FalseStep4 : (msg₁ : Msg)(sig₁ : ℕ) (b : Bool)
           → compareSigsMultiSigAux msg₁ [] [] sig₁ b ≡
              extractedFunctionPMSauxStep1FalseStep2TrueStep3FalseStep4 b
lemmaExtractedFunctionPMSauxStep1FalseStep2TrueStep3FalseStep4 msg₁ sig₁ true = refl
lemmaExtractedFunctionPMSauxStep1FalseStep2TrueStep3FalseStep4 msg₁ sig₁ false = refl

lemmaExtractedFunctionPMSauxStep1FalseStep2TrueStep3 : (pbk₄ : ℕ)(msg₁ : Msg)(sig₁ : ℕ)(b : Bool) →
      compareSigsMultiSigAux msg₁ [] (pbk₄ ∷ []) sig₁  b  ≡
      extractedFunctionPMSauxStep1FalseStep2TrueStep3 pbk₄ msg₁ sig₁ b

lemmaExtractedFunctionPMSauxStep1FalseStep2TrueStep3 pbk₄ msg₁ sig₁ true = refl
lemmaExtractedFunctionPMSauxStep1FalseStep2TrueStep3 pbk₄ msg₁ sig₁ false =
                lemmaExtractedFunctionPMSauxStep1FalseStep2TrueStep3FalseStep4 msg₁ sig₁ (param .signed msg₁ sig₁ pbk₄)

lemmaExtractedFunctionPMSauxStep1FalseStep2 : (pbk₃ pbk₄ : ℕ)(msg₁ : Msg)(sig₁ sig₂ : ℕ)(b : Bool) →
      compareSigsMultiSigAux msg₁ (sig₁ ∷ []) (pbk₃ ∷ pbk₄ ∷ []) sig₂  b ≡
         extractedFunctionPMSauxStep1FalseStep2 pbk₃ pbk₄ msg₁ sig₁ sig₂ b
lemmaExtractedFunctionPMSauxStep1FalseStep2 pbk₃ pbk₄ msg₁ sig₁ sig₂ false = lemmaExtractedFunctionPMSauxStep1FalseStep2FalseStep3 pbk₄ msg₁ sig₁ sig₂ ((param .signed msg₁ sig₂ pbk₃))
lemmaExtractedFunctionPMSauxStep1FalseStep2 pbk₃ pbk₄ msg₁ sig₁ sig₂ true = lemmaExtractedFunctionPMSauxStep1FalseStep2TrueStep3 pbk₄ msg₁ sig₁ (param .signed msg₁ sig₁ pbk₃)
-- pbk₄ msg₁ sig₁ sig₂ ((param .signed msg₁ sig₂ pbk₃))

lemmaExtractedFunctionPMSauxStep1TrueStep2FalseStep3FalseStep4 : (msg₁ : Msg)(sig₁ : ℕ)(b : Bool) →
          compareSigsMultiSigAux msg₁ [] [] sig₁ b ≡
          extractedFunctionPMSauxStep1TrueStep2FalseStep3FalseStep4 b
lemmaExtractedFunctionPMSauxStep1TrueStep2FalseStep3FalseStep4 msg₁ sig₁ true = refl
lemmaExtractedFunctionPMSauxStep1TrueStep2FalseStep3FalseStep4 msg₁ sig₁ false = refl

lemmaExtractedFunctionPMSauxStep1TrueStep2FalseStep3 : (pbk₄ : ℕ)(msg₁ : Msg)(sig₁ : ℕ)(b : Bool) →
          compareSigsMultiSigAux msg₁ [] (pbk₄ ∷ []) sig₁ b ≡
          extractedFunctionPMSauxStep1TrueStep2FalseStep3 pbk₄ msg₁ sig₁ b
lemmaExtractedFunctionPMSauxStep1TrueStep2FalseStep3 pbk₄ msg₁ sig₁ true = refl
lemmaExtractedFunctionPMSauxStep1TrueStep2FalseStep3 pbk₄ msg₁ sig₁ false = lemmaExtractedFunctionPMSauxStep1TrueStep2FalseStep3FalseStep4 msg₁ sig₁
                                                                              (param .signed msg₁ sig₁ pbk₄)

lemmaExtractedFunctionPMSauxStep1TrueStep2 : (pbk₃ pbk₄ : ℕ)(msg₁ : Msg)(sig₁ : ℕ)(b : Bool) →
       compareSigsMultiSigAux msg₁ [] (pbk₃ ∷ pbk₄ ∷ []) sig₁ b ≡
       extractedFunctionPMSauxStep1TrueStep2 pbk₃ pbk₄ msg₁ sig₁ b
lemmaExtractedFunctionPMSauxStep1TrueStep2 pbk₃ pbk₄ msg₁ sig₁ true = refl
lemmaExtractedFunctionPMSauxStep1TrueStep2 pbk₃ pbk₄ msg₁ sig₁ false = lemmaExtractedFunctionPMSauxStep1TrueStep2FalseStep3 pbk₄ msg₁ sig₁
                                                                         (param .signed msg₁ sig₁ pbk₃)


lemmaExtractedFunctionPMSauxStep1 : (pbk₂ pbk₃ pbk₄ : ℕ)(msg₁ : Msg)(sig₁  sig₂ : ℕ)(b : Bool) →
       compareSigsMultiSigAux msg₁ (sig₁ ∷ []) (pbk₂ ∷ pbk₃ ∷ pbk₄ ∷ []) sig₂  b ≡
       extractedFunctionPMSauxStep1 pbk₂ pbk₃ pbk₄ msg₁ sig₁ sig₂  b
lemmaExtractedFunctionPMSauxStep1 pbk₂ pbk₃ pbk₄ msg₁ sig₁ sig₂ false = lemmaExtractedFunctionPMSauxStep1FalseStep2 pbk₃ pbk₄ msg₁ sig₁ sig₂ (param .signed msg₁ sig₂ pbk₂)
lemmaExtractedFunctionPMSauxStep1 pbk₂ pbk₃ pbk₄ msg₁ sig₁ sig₂ true = {!lemmaExtractedFunctionPMSauxStep1TrueStep2 pbk₃ pbk₄ msg₁ sig₂ (param .signed msg₁ sig₂ pbk₃)!}


test : Set
test = {!!}
