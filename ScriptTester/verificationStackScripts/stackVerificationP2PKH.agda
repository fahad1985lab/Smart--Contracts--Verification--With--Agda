open import basicBitcoinDataType

module  verificationStackScripts.stackVerificationP2PKH (param : GlobalParameters) where

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
open import Data.List.NonEmpty hiding (head; [_])
open import Data.Nat using (ℕ; _+_; _≥_; _>_; zero; suc; s≤s; z≤n)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality


--our libraries
open import libraries.andLib
open import libraries.miscLib
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

accept₄ : ℕ → StackStatePred
accept₄ pbk  = stackPred2SPred (accept₄ˢ pbk)

accept₅ : ℕ → StackStatePred
accept₅ pbk  = stackPred2SPred (accept₅ˢ pbk)

-- accept-6 : ℕ → StackStatePred
-- accept-6 pbkHash  = stackPred2SPred (wPreCondP2PKHˢ pbkHash)

wPreCondP2PKH : (pbkh : ℕ)  → StackStatePred
wPreCondP2PKH pbkh  = stackPred2SPred (wPreCondP2PKHˢ pbkh)


correct-1-to : (s : StackState) → accept₁ s → (accept-0 ⁺) (⟦ opCheckSig ⟧s s )
correct-1-to ⟨ time , msg₁ , pbk  ∷ sig ∷ st ⟩ p =  boolToNatNotFalseLemma (isSigned  msg₁ sig pbk) p


correct-1-from : (s : StackState) → (accept-0 ⁺) (⟦ opCheckSig ⟧s s ) → accept₁ s
correct-1-from ⟨ time , msg₁ , pbk ∷ sig ∷ stack₁  ⟩ p = boolToNatNotFalseLemma2 (isSigned  msg₁ sig pbk) p
--correctone
correct-1 : < accept₁ >iff  ([ opCheckSig ]) < acceptState >
correct-1 .==> = correct-1-to
correct-1 .<== = correct-1-from


correct-2-to : (s : StackState) → accept₂ s → (accept₁ ⁺) (⟦ opVerify ⟧s s )
correct-2-to ⟨ time , msg₁ , suc x ∷ x₁ ∷ x₂ ∷ stack₁ ⟩ p = p

correct-2-from : (s : StackState) → (accept₁ ⁺) (⟦ opVerify ⟧s s ) → accept₂ s
correct-2-from ⟨ time , msg₁ , suc x ∷ x₁ ∷ x₂ ∷ stack₁ ⟩ p = p

--correcttwo
correct-2 : < accept₂ >iff  ([ opVerify ]) < accept₁ >
correct-2 .==> = correct-2-to
correct-2 .<== = correct-2-from


correct-3-to : (s : StackState) → accept₃ s → (accept₂ ⁺) (⟦ opEqual ⟧s s )
correct-3-to ⟨ time , msg₁ , pbk1  ∷ .pbk1 ∷ pbk2 ∷  sig ∷ []  ⟩ (conj refl checkSig)  rewrite ( lemmaCompareNat pbk1 ) =  checkSig
correct-3-to ⟨ time , msg₁ , pbk1 ∷ .pbk1 ∷ pbk2  ∷ sig ∷ x ∷ rest  ⟩ (conj refl checkSig) rewrite  ( lemmaCompareNat pbk1 ) = checkSig

correct-3-from  : (s : StackState)  → (accept₂ ⁺) (⟦ opEqual ⟧s s ) → accept₃ s
correct-3-from ⟨ time , msg₁ , x ∷ x₁ ∷ pbk ∷ sig ∷ stack₁  ⟩ p rewrite ( lemmaCorrect3From x x₁ pbk sig time msg₁ p )
  =   let
        q : True (isSigned  msg₁ sig pbk)
        q = correct3Aux2 (compareNaturals x x₁) pbk sig stack₁ time msg₁ p
      in (conj refl q)

--correctthree
correct-3 : < accept₃ >iff  ([ opEqual ]) < accept₂ >
correct-3 .==> = correct-3-to
correct-3 .<== = correct-3-from

correct-4-to : ( pbk : ℕ ) →  (s : StackState) → accept₄ pbk  s → (accept₃ ⁺) (⟦ opPush pbk ⟧s s )
correct-4-to pbk ⟨ currentTime₁ , msg₁ , .pbk ∷ x₁ ∷ x₂ ∷ stack₁ ⟩ (conj refl and4) = conj refl and4


correct-4-from : ( pbk : ℕ ) →  (s : StackState) → (accept₃ ⁺) (⟦ opPush pbk ⟧s s ) → accept₄ pbk  s
correct-4-from pbk ⟨ currentTime₁ , msg₁ , .pbk ∷ x₁ ∷ x₂ ∷ stack₁   ⟩ (conj refl and4) = conj refl and4

--correctfour
correct-4 :( pbk : ℕ ) →  < accept₄ pbk >iff  ([ opPush pbk ]) < accept₃ >
correct-4 pbk .==> = correct-4-to pbk
correct-4 pbk .<== = correct-4-from pbk


correct-5-to : (pbk : ℕ ) → (s : StackState) → accept₅ pbk s →  (( accept₄ pbk ) ⁺) (⟦ opHash ⟧s s )
correct-5-to pbk ⟨ time , msg₁ , x ∷ x₁ ∷ x₂ ∷ stack₁ ⟩ (conj refl checkSig) = (conj refl checkSig)

correct-5-from : ( pbk : ℕ ) →  (s : StackState)  → (( accept₄ pbk) ⁺) (⟦ opHash ⟧s s ) → accept₅ pbk  s
correct-5-from .(hashFun x) ⟨ time , msg₁ , x ∷ x₁ ∷ x₂ ∷ stack₁ ⟩ (conj refl checkSig) = conj refl checkSig

--correctfive
correct-5 :( pbk : ℕ ) →  < accept₅ pbk >iff  ([ opHash  ]) < accept₄ pbk >
correct-5 pbk .==> = correct-5-to pbk
correct-5 pbk .<== = correct-5-from pbk


correct-6-to : (pbkHash : ℕ ) → (s : StackState) → wPreCondP2PKH pbkHash s →  (( accept₅ pbkHash ) ⁺) (⟦ opDup ⟧s s )
correct-6-to pbkHash ⟨ time , msg₁ , x ∷ x₁ ∷ [] ⟩ p = p
correct-6-to pbkHash ⟨ time , msg₁ , x ∷ x₁ ∷ x₂ ∷ stack₁ ⟩ p = p

correct-6-from : ( pbkHash : ℕ ) →  (s : StackState)  → (( accept₅ pbkHash) ⁺) (⟦ opDup ⟧s s ) → wPreCondP2PKH pbkHash  s
correct-6-from pbkHash ⟨ time , msg₁ , x ∷ x₁ ∷ stack₁ ⟩ p = p

--correctsix
correct-6 :( pbk : ℕ ) →  < wPreCondP2PKH pbk >iff  ([ opDup  ]) < accept₅ pbk >
correct-6 pbk .==> = correct-6-to pbk
correct-6 pbk .<== = correct-6-from pbk



--scriptppkh
scriptP2PKHᵇ : (pbkh : ℕ) → BitcoinScriptBasic
scriptP2PKHᵇ pbkh = opDup ∷ opHash ∷ (opPush pbkh) ∷ opEqual ∷ opVerify ∷ [ opCheckSig ]


{- Reminder  from stackPredicate.agda


-- acceptingBasic means that the stack has at hight >= 1 and top element >0
acceptingBasic : Time → Msg → Stack → Bool
acceptingBasic time msg₁ [] = false
acceptingBasic time msg₁ (x ∷ stack₁) = notFalse x


acceptStateˢ : StackPredicate
acceptStateˢ time msg₁ s = acceptingBasic time msg₁ s)


-- wPreCondP2PKHˢ expresses:
--    stack has height at least 2
--    for the two top elements pbk and sig we have
--    hashFun pbk ≡  pbkh   and   isSigned  m sig pbk
wPreCondP2PKHˢ : (pbkh : ℕ ) → StackPredicate
wPreCondP2PKHˢ pbkh time m [] = ⊥
wPreCondP2PKHˢ pbkh time m (x ∷ []) = ⊥
wPreCondP2PKHˢ pbkh time m ( pbK ∷ sig ∷ st)
    =  (hashFun pbk ≡  pbkh ) ∧  True ( isSigned  m sig pbk )

-}


-- acceptState : StackStatePred
-- acceptState = stackPred2SPred acceptStateˢ -- accept-0Basic

-- acceptState = accept-0Basic

-- wPreCondP2PKH pbkh = accept-6 pbkh


--main theorem P2PKH
theoremP2PKH : (pbkh : ℕ) → < wPreCondP2PKH pbkh >iff scriptP2PKHᵇ pbkh < acceptState >
theoremP2PKH pbkh  = wPreCondP2PKH pbkh <><>⟨ [ opDup ]   ⟩⟨  correct-6  pbkh  ⟩
                     accept₅  pbkh  <><>⟨  [  opHash ]       ⟩⟨  correct-5  pbkh  ⟩
                     accept₄  pbkh  <><>⟨  [  opPush pbkh ]  ⟩⟨  correct-4  pbkh  ⟩
                     accept₃        <><>⟨  [  opEqual ]      ⟩⟨  correct-3  ⟩
                     accept₂        <><>⟨  [  opVerify ]     ⟩⟨  correct-2  ⟩
                     accept₁        <><>⟨  [  opCheckSig ]   ⟩⟨  correct-1  ⟩e  acceptState  ∎p


{- We have natural accepting condition expressing that the stack has height >= 1 and top element > 0
   We have a natural weakest precondition expressing  blablabla
   and a proof that it is the weakest precondtion for the scriptP2PKH w.r.t. the acceptState

   NOTE:  here we used single instructions. However opPush pbkh is already a composed instruction
          and we could use whole program pieces instead of single instructions.

          The complication is due to the fact that instructions can lead to failure, and therefore
             the operational semantics of the resulting programs become quite long and complicated
             because if we have   instructions p1 p2 p3  in Agda syntax we get
             [[ p1 :: p2 :: p3 ::[] ]]s =
                case [[ p1 ]]s  of
                   nothing -> nothing
                   just s1 -> case [[ p2 ]] s1 of
                                nothing -> nothing
                                just s2 -> [[ p3 ]] s2
            So one gets a very involved case distinction which quickly becomes difficult to view.
            By having intermediate conditions we make this manageable.



Not for paper:
Current agda we have

f  zero   = ??
f (suc y) = ??

in Agda1 we had
f x =  case x of
            zero -> ??
            suc y -> ??

-}
