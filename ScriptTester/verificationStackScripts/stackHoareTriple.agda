open import basicBitcoinDataType

module verificationStackScripts.stackHoareTriple (param : GlobalParameters) where

open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_)
open import Data.Sum
open import Data.Maybe
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Bool.Base hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality


-- our libraries
open import libraries.listLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.andLib
open import libraries.miscLib
open import libraries.maybeLib
open import libraries.emptyLib
open import libraries.equalityLib


open import stack
open import instructionBasic
open import verificationStackScripts.stackState
open import verificationStackScripts.sPredicate
open import verificationStackScripts.semanticsStackInstructions param
open import verificationStackScripts.stackVerificationLemmas param









_<_>_  : BStackStatePred →  BitcoinScriptBasic →  BStackStatePred →  Set
ϕ < P > ψ = (s : StackState) → True (ϕ s) → True( (ψ ⁺ᵇ) ( ⟦ P ⟧ s))


weakestPreCond  :  (Postcond : BStackStatePred) → BitcoinScriptBasic →  BStackStatePred
weakestPreCond ψ P state =  (ψ ⁺ᵇ) ( ⟦ P ⟧ state)



record <_>iff_<_>  (P : StackStatePred)(p : BitcoinScriptBasic)(Q : StackStatePred) : Set where
  constructor hoare3
  field
    ==> : (s : StackState) → P s → (Q ⁺) (⟦ p ⟧ s )
    <== : (s : StackState) → (Q ⁺) (⟦ p ⟧ s ) → P s

open <_>iff_<_>  public


record _<=>p_ (φ ψ : StackStatePred) : Set where
  constructor equivp
  field
    ==>e  : (s : StackState) → φ s → ψ s
    <==e  : (s : StackState) → ψ s →  φ s
open _<=>p_ public


refl<=>  :   (φ : StackStatePred)
            →  φ <=>p φ
refl<=> φ  .==>e s x  =  x
refl<=> φ  .<==e s x = x


sym<=>  :   (φ ψ : StackStatePred)
            →  φ <=>p ψ
            →  ψ <=>p φ
sym<=> φ ψ (equivp ==>e₁ <==e₁) .==>e  = <==e₁
sym<=> φ ψ (equivp ==>e₁ <==e₁) .<==e  = ==>e₁


trans<=>  :   (φ ψ ψ' : StackStatePred)
            →  φ <=>p ψ
            →  ψ <=>p ψ'
            →  φ <=>p ψ'
trans<=> φ ψ ψ' (equivp ==>e₁ <==e₁) (equivp ==>e₂ <==e₂) .==>e s p =  ==>e₂ s (==>e₁ s p)
trans<=> φ ψ ψ' (equivp ==>e₁ <==e₁) (equivp ==>e₂ <==e₂) .<==e s p = <==e₁ s (<==e₂ s p)




⊎HoareLemma1 : {φ ψ ψ' : StackStatePred}(p : BitcoinScriptBasic)
                  → < φ >iff  p  < ψ >
                  → < ⊥p >iff  p  < ψ' >
                  → < φ >iff p < ψ ⊎p ψ' >
⊎HoareLemma1 {φ} {ψ} {ψ'} p (hoare3 c1 c2) c .==> s q = lemma⊎pleft ψ  ψ' (⟦ p ⟧ s) (c1 s q)
⊎HoareLemma1 {φ} {ψ} {ψ'} p (hoare3 ==>₁ <==₁) (hoare3 ==>₂ <==₂) .<== s q
          = let
              r : (ψ' ⁺) (⟦ p ⟧ s) → φ s
              r x = efq (<==₂ s x)
            in lemma⊎pinv ψ  ψ' (φ s) (⟦ p ⟧ s) (<==₁ s) r q


⊎HoareLemma2 : {φ φ' ψ ψ' : StackStatePred}(p : BitcoinScriptBasic)
                  → < φ >iff  p  < ψ >
                  → < φ' >iff  p  < ψ' >
                  → < φ ⊎p φ' >iff p < ψ ⊎p ψ' >
⊎HoareLemma2 {φ} {φ'} {ψ} {ψ'} prog (hoare3 ==>₁ <==₁) (hoare3 ==>₂ <==₂) .==> s (inj₁ q)
          = lemma⊎pleft ψ ψ' (⟦ prog ⟧ s) (==>₁ s q)
⊎HoareLemma2 {φ} {φ'} {ψ} {ψ'} prog (hoare3 ==>₁ <==₁) (hoare3 ==>₂ <==₂) .==> s (inj₂ q)
           = lemma⊎pright ψ ψ' (⟦ prog ⟧ s) (==>₂ s q)
⊎HoareLemma2 {φ} {φ'} {ψ} {ψ'} prog (hoare3 ==>₁ <==₁) (hoare3 ==>₂ <==₂) .<== s q
          = let
              q1 : (ψ ⁺) (⟦ prog ⟧ s) → φ s ⊎ φ' s
              q1 x = inj₁ (<==₁ s x)

              q2 : (ψ' ⁺) (⟦ prog ⟧ s) → φ s ⊎ φ' s
              q2 x = inj₂ (<==₂ s x)
            in lemma⊎pinv ψ  ψ' ((φ ⊎p φ') s) (⟦ prog ⟧ s) q1 q2 q



predEquivr : (φ ψ ψ' : StackStatePred)
             (prog : BitcoinScriptBasic)
             → < φ >iff prog < ψ >
             → ψ <=>p ψ'
             → < φ >iff prog < ψ' >
predEquivr φ ψ ψ' prog (hoare3 ==>₁ <==₁) (equivp ==>e <==e) .==> s p1
  = liftPredtransformerMaybe ψ ψ' ==>e (⟦ prog ⟧ s) (==>₁ s p1)
predEquivr φ ψ ψ' prog (hoare3 ==>₁ <==₁) (equivp ==>e <==e) .<== s p1
             = let
                 subgoal : (ψ ⁺) (⟦ prog ⟧ s)
                 subgoal =  liftPredtransformerMaybe ψ' ψ <==e (⟦ prog ⟧ s) p1
                 goal : φ s
                 goal = <==₁ s subgoal
               in goal

predEquivl : (φ φ' ψ : StackStatePred)
             (prog : BitcoinScriptBasic)
             → φ <=>p φ'
             → < φ' >iff prog < ψ >
             → < φ >iff prog < ψ >
predEquivl φ φ' ψ prog (equivp ==>e <==e) (hoare3 ==>₁ <==₁) .==> s p1
             = let
                 goal : (ψ ⁺) (⟦ prog ⟧ s)
                 goal = ==>₁ s (==>e s p1)
               in goal
predEquivl φ φ' ψ prog (equivp ==>e <==e) (hoare3 ==>₁ <==₁) .<== s p1
              = let
                  subgoal : φ' s
                  subgoal = <==₁ s p1
                  goal : φ s
                  goal = <==e s subgoal
                in goal


equivPreds⊎ : (φ ψ ψ' : StackStatePred)
             → (φ ∧p (ψ ⊎p ψ')) <=>p ((φ ∧p ψ ) ⊎p (φ ∧p ψ'))

equivPreds⊎ φ ψ ψ' .==>e s (conj and4 (inj₁ x)) = inj₁ (conj and4 x)
equivPreds⊎ φ ψ ψ' .==>e s (conj and4 (inj₂ y)) = inj₂ (conj and4 y)
equivPreds⊎ φ ψ ψ' .<==e s (inj₁ (conj and4 and5)) = conj and4 (inj₁ and5)
equivPreds⊎ φ ψ ψ' .<==e s (inj₂ (conj and4 and5)) = conj and4 (inj₂ and5)

equivPreds⊎Rev : (φ ψ ψ' : StackStatePred)
             →  ((φ ∧p ψ ) ⊎p (φ ∧p ψ'))  <=>p (φ ∧p (ψ ⊎p ψ'))

equivPreds⊎Rev φ ψ ψ' .==>e s (inj₁ (conj and4 and5)) = conj and4 (inj₁ and5)
equivPreds⊎Rev φ ψ ψ' .==>e s (inj₂ (conj and4 and5)) = conj and4 (inj₂ and5)
equivPreds⊎Rev φ ψ ψ' .<==e s (conj and4 (inj₁ x)) = inj₁ (conj and4 x)
equivPreds⊎Rev φ ψ ψ' .<==e s (conj and4 (inj₂ y)) = inj₂ (conj and4 y)


_++ho_ : {P Q R : StackStatePred}{p q : BitcoinScriptBasic} → < P >iff p < Q >  → < Q >iff q < R > → < P >iff p ++  q < R >
_++ho_ {P} {Q} {R} {p} {q} pproof qproof .==> = bindTransformer-toSequence P Q R p q (pproof .==>)  (qproof .==>)
_++ho_ {P} {Q} {R} {p} {q} pproof qproof .<== = bindTransformer-fromSequence P Q R p q (pproof .<==)  (qproof .<==)

_++hoeq_ : {P Q R : StackStatePred}{p : BitcoinScriptBasic} → < P >iff p < Q >  → < Q >iff [] < R > → < P >iff p  < R >
_++hoeq_ {P} {Q} {R} {p} pproof qproof .==> = bindTransformer-toSequenceeq P Q R p (pproof .==>)  (qproof .==>)
_++hoeq_ {P} {Q} {R} {p} pproof qproof .<== = bindTransformer-fromSequenceeq P Q R p (pproof .<==)  (qproof .<==)


module HoareReasoning  where
  infix  3 _∎p
  infixr 2 step-<><>  step-<><>e step-<=>

  _∎p : ∀ (φ : StackStatePred) → < φ >iff [] < φ >
  (φ ∎p) .==>  s p = p
  (φ ∎p) .<==  s p = p


  step-<><> : ∀ {φ ψ ρ : StackStatePred}(p : BitcoinScriptBasic){q : BitcoinScriptBasic}
             → < φ >iff p < ψ >
             → < ψ >iff q < ρ >
             → < φ >iff p ++ q < ρ >
  step-<><>  {φ} {ψ} {ρ} p φpψ ψqρ = φpψ ++ho ψqρ

  step-<><>e : ∀ {φ ψ ρ : StackStatePred}(p : BitcoinScriptBasic)
             → < φ >iff p < ψ >
             → < ψ >iff [] < ρ >
             → < φ >iff p  < ρ >
  step-<><>e  p φpψ ψqρ = φpψ ++hoeq ψqρ





  step-<=> : ∀ {φ ψ ρ : StackStatePred}{p : BitcoinScriptBasic}
             → φ <=>p ψ
             → < ψ >iff p < ρ >
             → < φ >iff p < ρ >
  step-<=>  {φ} {ψ} {ρ} {p} φψ ψqρ = predEquivl φ ψ ρ p φψ ψqρ




  syntax step-<><> {φ} p φψ ψρ = φ <><>⟨  p ⟩⟨ φψ ⟩ ψρ
  syntax step-<><>e {φ} p φψ ψρ = φ <><>⟨  p ⟩⟨ φψ ⟩e ψρ



  syntax step-<=>  {φ} φψ ψρ = φ <=>⟨  φψ ⟩ ψρ




open HoareReasoning public




⊥Lemmap : (p : BitcoinScriptBasic)
          → < ⊥p >iff  p  < ⊥p >
⊥Lemmap [] .==> s ()
⊥Lemmap p .<== s p' = liftToMaybeLemma⊥ (⟦ p ⟧ s)  p'


lemmaHoare[] : {φ : StackStatePred}
               → < φ >iff [] < φ >
lemmaHoare[]  .==> s p = p
lemmaHoare[]  .<== s p = p


-- a generic Hoare triple, which refers instead of an instruction to the
--    state transformer (f will be equal to  ⟦ instr ⟧s )
record <_>ssgen_<_> (φ : StackStatePred)(f : StackState → Maybe StackState)(ψ : StackStatePred) : Set where
  constructor hoareTripleSSGen
  field
    ==>g : (s : StackState) → φ s → (ψ ⁺) (f s )
    <==g : (s : StackState) → (ψ ⁺)  (f s ) → φ s

open <_>ssgen_<_>  public

{-
HoareTripleSSGen : (φ : StackStatePred)(f : StackState → Maybe StackState)(ψ : StackStatePred)
                   → Set
HoareTripleSSGen φ f ψ  = < φ >ssgen f < ψ  >
-}


lemmaTransferHoareTripleGen : (φ ψ : StackStatePred)
                              (f g : StackState → Maybe StackState)
                              (p : (s : StackState) → f s ≡ g s)
                              → < φ >ssgen f < ψ >
                              → < φ >ssgen g < ψ >
lemmaTransferHoareTripleGen φ ψ f g p (hoareTripleSSGen ==>g₁ <==g₁) .==>g s x₁
          = transfer (λ x → (ψ ⁺) x) (p s) (==>g₁ s x₁)
lemmaTransferHoareTripleGen φ ψ f g p (hoareTripleSSGen ==>g₁ <==g₁) .<==g s x₁
          = <==g₁ s (transfer (λ x → (ψ ⁺) x) (sym (p s)) x₁)
