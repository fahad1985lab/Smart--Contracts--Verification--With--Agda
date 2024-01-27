open import basicBitcoinDataType

module  verificationStackScripts.stackVerificationP2PKH (param : GlobalParameters) where

open import libraries.listLib
open import Data.List.Base
open import libraries.natLib
open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_)
open import Data.Unit  
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; _<_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_ ; _<_)
open import Data.List.NonEmpty hiding (head; [_])
open import Data.Nat using (ℕ; _+_; _≥_; _>_; zero; suc; s≤s; z≤n)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality


--our libraries
open import libraries.andLib
open import libraries.maybeLib
open import libraries.boolLib

open import stack
open import stackPredicate
open import semanticBasicOperations param
open import instructionBasic
open import verificationP2PKHbasic param
open import verificationStackScripts.stackHoareTriple param
open import verificationStackScripts.stackState
open import verificationStackScripts.sPredicate
open import verificationStackScripts.semanticsStackInstructions param
open import verificationStackScripts.stackVerificationLemmas param



-- note accept_0 is the same as acceptState
accept-0 : StackStatePred
accept-0 = stackPred2SPred accept-0Basic


accept₁ : StackStatePred
accept₁  = stackPred2SPred accept₁ˢ

accept₂ : StackStatePred
accept₂ = stackPred2SPred accept₂ˢ

accept₃ : StackStatePred
accept₃ = stackPred2SPred accept₃ˢ

-- checked needs to be pbkh not pbk
accept₄ : ℕ → StackStatePred
accept₄ pbkh  = stackPred2SPred (accept₄ˢ pbkh)

-- checked needs to be pbkh not pbk
accept₅ : ℕ → StackStatePred
accept₅ pbkh  = stackPred2SPred (accept₅ˢ pbkh)


-- checked needs to be pbkh not pbk
wPreCondP2PKH : (pbkh : ℕ)  → StackStatePred
wPreCondP2PKH pbkh  = stackPred2SPred (wPreCondP2PKHˢ pbkh)

-- we use pbk and not pbkh because that is what is provided by the unlocking script
correct-opCheckSig-to : (s : StackState) → accept₁ s → (accept-0 ⁺) (⟦ opCheckSig ⟧ₛ s )
correct-opCheckSig-to ⟨ time , msg₁ , pbk  ∷ sig ∷ st ⟩ p =  boolToNatNotFalseLemma (isSigned  msg₁ sig pbk) p


correct-opCheckSig-from : (s : StackState) → (accept-0 ⁺) (⟦ opCheckSig ⟧ₛ s ) → accept₁ s
correct-opCheckSig-from ⟨ time , msg₁ , pbk ∷ sig ∷ stack₁  ⟩ p = boolToNatNotFalseLemma2 (isSigned  msg₁ sig pbk) p



correct-opCheckSig : < accept₁ >ⁱᶠᶠ  ([ opCheckSig ]) < acceptState >
correct-opCheckSig .==> = correct-opCheckSig-to
correct-opCheckSig .<== = correct-opCheckSig-from


correct-opVerify-to : (s : StackState) → accept₂ s → (accept₁ ⁺) (⟦ opVerify ⟧ₛ s )
correct-opVerify-to ⟨ time , msg₁ , suc x ∷ x₁ ∷ x₂ ∷ stack₁ ⟩ p = p

correct-opVerify-from : (s : StackState) → (accept₁ ⁺) (⟦ opVerify ⟧ₛ s ) → accept₂ s
correct-opVerify-from ⟨ time , msg₁ , suc x ∷ x₁ ∷ x₂ ∷ stack₁ ⟩ p = p


correct-opVerify : < accept₂ >ⁱᶠᶠ  ([ opVerify ]) < accept₁ >
correct-opVerify .==> = correct-opVerify-to
correct-opVerify .<== = correct-opVerify-from



correct-opEqual-to : (s : StackState) → accept₃ s → (accept₂ ⁺) (⟦ opEqual ⟧ₛ s )
correct-opEqual-to ⟨ time , msg₁ , pbk1  ∷ .pbk1 ∷ pbk2 ∷  sig ∷ []  ⟩ (conj refl checkSig)  rewrite ( lemmaCompareNat pbk1 ) =  checkSig
correct-opEqual-to ⟨ time , msg₁ , pbk1 ∷ .pbk1 ∷ pbk2  ∷ sig ∷ x ∷ rest  ⟩ (conj refl checkSig) rewrite  ( lemmaCompareNat pbk1 ) = checkSig

correct-opEqual-from  : (s : StackState)  → (accept₂ ⁺) (⟦ opEqual ⟧ₛ s ) → accept₃ s
correct-opEqual-from ⟨ time , msg₁ , x ∷ x₁ ∷ pbk ∷ sig ∷ stack₁  ⟩ p rewrite ( lemmaCorrect3From x x₁ pbk sig time msg₁ p )
  =   let
        q : True (isSigned  msg₁ sig pbk)
        q = correct3Aux2 (compareNaturals x x₁) pbk sig stack₁ time msg₁ p
      in (conj refl q)



correct-opEqual : < accept₃ >ⁱᶠᶠ  ([ opEqual ]) < accept₂ >
correct-opEqual .==> = correct-opEqual-to
correct-opEqual .<== = correct-opEqual-from



-- needs to be pbkh since opPush refers to it
correct-opPush-to : ( pbkh : ℕ ) →  (s : StackState) → accept₄ pbkh  s → (accept₃ ⁺) (⟦ opPush pbkh ⟧ₛ s )
correct-opPush-to pbkh ⟨ currentTime₁ , msg₁ , .pbkh ∷ x₁ ∷ x₂ ∷ stack₁ ⟩ (conj refl and4) = conj refl and4


correct-opPush-from : ( pbkh : ℕ ) →  (s : StackState) → (accept₃ ⁺) (⟦ opPush pbkh ⟧ₛ s ) → accept₄ pbkh  s
correct-opPush-from pbkh ⟨ currentTime₁ , msg₁ , .pbkh ∷ x₁ ∷ x₂ ∷ stack₁   ⟩ (conj refl and4) = conj refl and4


correct-opPush :( pbkh : ℕ ) →  < accept₄ pbkh >ⁱᶠᶠ  ([ opPush pbkh ]) < accept₃ >
correct-opPush pbkh .==> = correct-opPush-to pbkh
correct-opPush pbkh .<== = correct-opPush-from pbkh



-- needs to be pbkh since accept₄ and accept₅ refer to pbkh
correct-opHash-to : (pbkh : ℕ ) → (s : StackState) → accept₅ pbkh s →  (( accept₄ pbkh ) ⁺) (⟦ opHash ⟧ₛ s )
correct-opHash-to pbkh ⟨ time , msg₁ , x ∷ x₁ ∷ x₂ ∷ stack₁ ⟩ (conj refl checkSig) = (conj refl checkSig)

correct-opHash-from : ( pbkh : ℕ ) →  (s : StackState)  → (( accept₄ pbkh) ⁺) (⟦ opHash ⟧ₛ s ) → accept₅ pbkh  s
correct-opHash-from .(hashFun x) ⟨ time , msg₁ , x ∷ x₁ ∷ x₂ ∷ stack₁ ⟩ (conj refl checkSig) = conj refl checkSig


correct-opHash :( pbkh : ℕ ) →  < accept₅ pbkh >ⁱᶠᶠ  ([ opHash  ]) < accept₄ pbkh >
correct-opHash pbkh .==> = correct-opHash-to pbkh
correct-opHash pbkh .<== = correct-opHash-from pbkh



-- needs to be pbkh since accept₅ refer to pbkh
correct-opDup-to : (pbkh : ℕ ) → (s : StackState) → wPreCondP2PKH pbkh s →  (( accept₅ pbkh ) ⁺) (⟦ opDup ⟧ₛ s )
correct-opDup-to pbkh ⟨ time , msg₁ , x ∷ x₁ ∷ [] ⟩ p = p
correct-opDup-to pbkh ⟨ time , msg₁ , x ∷ x₁ ∷ x₂ ∷ stack₁ ⟩ p = p

correct-opDup-from : ( pbkh : ℕ ) →  (s : StackState)  → (( accept₅ pbkh) ⁺) (⟦ opDup ⟧ₛ s ) → wPreCondP2PKH pbkh  s
correct-opDup-from pbkh ⟨ time , msg₁ , x ∷ x₁ ∷ stack₁ ⟩ p = p


correct-opDup :( pbkh : ℕ ) →  < wPreCondP2PKH pbkh >ⁱᶠᶠ  ([ opDup  ]) < accept₅ pbkh >
correct-opDup pbkh .==> = correct-opDup-to pbkh
correct-opDup pbkh .<== = correct-opDup-from pbkh


-- P2PKH script refers to pbkh not pbk
scriptP2PKHᵇ : (pbkh : ℕ) → BitcoinScriptBasic
scriptP2PKHᵇ pbkh = opDup ∷ opHash ∷ (opPush pbkh) ∷ opEqual ∷ opVerify ∷ [ opCheckSig ]


--main theorem for P2PKH
theoremP2PKH :  (pbkh : ℕ)
                → < wPreCondP2PKH pbkh >ⁱᶠᶠ scriptP2PKHᵇ pbkh < acceptState >
theoremP2PKH pbkh  = wPreCondP2PKH pbkh <><>⟨ [ opDup ]      ⟩⟨  correct-opDup  pbkh ⟩
                     accept₅  pbkh  <><>⟨  [  opHash ]       ⟩⟨  correct-opHash pbkh ⟩
                     accept₄  pbkh  <><>⟨  [  opPush pbkh ]  ⟩⟨  correct-opPush pbkh ⟩
                     accept₃        <><>⟨  [  opEqual ]      ⟩⟨  correct-opEqual     ⟩
                     accept₂        <><>⟨  [  opVerify ]     ⟩⟨  correct-opVerify    ⟩
                     accept₁        <><>⟨  [  opCheckSig ]   ⟩⟨  correct-opCheckSig  ⟩e
                                    acceptState  ∎p
