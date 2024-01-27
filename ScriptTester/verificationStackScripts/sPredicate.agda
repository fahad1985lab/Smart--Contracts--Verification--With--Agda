open import basicBitcoinDataType

module verificationStackScripts.sPredicate where

open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  
open import Data.Empty
open import Data.Sum
open import Data.Maybe
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Bool.Base hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
open import Data.List.NonEmpty hiding (head)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality



--our libraries
open import libraries.listLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.andLib
open import libraries.maybeLib


open import stack
open import stackPredicate
open import verificationStackScripts.stackState




BStackStatePred  : Set
BStackStatePred =  StackState →  Bool



MaybeBStackStatePred : Set
MaybeBStackStatePred = Maybe StackState →  Bool


-- Stack Predicate
StackStatePred : Set₁
StackStatePred = StackState → Set



predicateAfterPushingx : (n : ℕ)(φ : StackStatePred) → StackStatePred
predicateAfterPushingx n φ ⟨ time , msg₁ , stack₁ ⟩ = φ ⟨ time , msg₁ , n ∷ stack₁ ⟩


predicateForTopElOfStack : (n : ℕ) → StackStatePred
predicateForTopElOfStack n ⟨ time , msg₁ , [] ⟩ = ⊥
predicateForTopElOfStack n ⟨ time , msg₁ , x ∷ stack₁ ⟩ = x ≡ n



_∧p_ : ( φ ψ  : StackStatePred ) → StackStatePred
(φ ∧p ψ ) s  =  φ s  ∧  ψ s



⊥p : StackStatePred
⊥p s = ⊥

infixl 4 _⊎p_

_⊎p_   : (φ ψ : StackStatePred) → StackStatePred
(φ ⊎p ψ) s = φ s ⊎ ψ s



lemma⊎pleft : (ψ ψ' : StackStatePred)(s : Maybe StackState)
              → (ψ ⁺) s → ( (ψ ⊎p ψ') ⁺) s
lemma⊎pleft ψ ψ' (just x) p = inj₁ p

lemma⊎pright : (ψ ψ' : StackStatePred) (s : Maybe StackState)
               → (ψ' ⁺) s → (( ψ ⊎p ψ' ) ⁺ ) s
lemma⊎pright  ψ ψ' (just x) p = inj₂ p

lemma⊎pinv : (ψ ψ' : StackStatePred)(A : Set) (s : Maybe StackState)
             → ((ψ ⁺) s  → A)
             → ((ψ' ⁺) s  → A)
             →  ((ψ ⊎p ψ') ⁺) s → A
lemma⊎pinv ψ ψ' A (just x) p q (inj₁ x₁) = p x₁
lemma⊎pinv ψ ψ' A (just x) p q (inj₂ y) = q y




stackPred2SPred : StackPredicate → StackStatePred
stackPred2SPred f ⟨ time , msg₁ , stack₁ ⟩ = f time msg₁ stack₁



stackPred2SPredBool : ( Time → Msg → Stack → Bool ) → (  StackState →  Bool )
stackPred2SPredBool f ⟨ currentTime₁ , msg₁ , stack₁ ⟩
              = f currentTime₁ msg₁ stack₁



topElStack=0 : StackStatePred
topElStack=0 ⟨ time , msg₁ , [] ⟩ = ⊥
topElStack=0 ⟨ time , msg₁ , zero ∷ stack₁ ⟩ = ⊤
topElStack=0 ⟨ time , msg₁ , suc x ∷ stack₁ ⟩ = ⊥



truePred : StackPredicate → StackStatePred
truePred φ = stackPred2SPred (truePredaux  φ)



falsePredaux : StackPredicate → StackPredicate
falsePredaux φ time msg [] = ⊥
falsePredaux φ time msg (zero ∷ st) = φ time msg  st
falsePredaux φ time msg (suc x ∷ st) = ⊥

falsePred : StackPredicate → StackStatePred
falsePred φ = stackPred2SPred (falsePredaux  φ)


liftAddingx : (n : ℕ)( φ : StackPredicate ) →  StackStatePred
liftAddingx n φ = predicateAfterPushingx n (stackPred2SPred φ)





acceptState : StackStatePred
acceptState = stackPred2SPred acceptStateˢ
