open import basicBitcoinDataType

module verificationStackScripts.stackVerificationLemmas (param : GlobalParameters) where

open import libraries.listLib
open import libraries.natLib
open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_)
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Maybe
open import Data.Bool  hiding (_≤_ ; _<_ ; if_then_else_ )
                       renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_ ; _<_)
open import Data.List.NonEmpty hiding (head )
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
open import instructionBasic
open import verificationStackScripts.stackState
open import verificationStackScripts.sPredicate
open import verificationStackScripts.semanticsStackInstructions param



liftCondOperation2Program-to-simple : (accept2 : StackStatePred)
  (op : InstructionBasic)  (s : StackState)
  → (accept2 ⁺) (⟦ op ⟧ₛ s )
  → (accept2 ⁺) (⟦ op ∷ [] ⟧ s )
liftCondOperation2Program-to-simple accept2 op s a = a

liftCondOperation2Program-from-simple : (accept2 : StackStatePred)
  (op : InstructionBasic)  (s : StackState)
  → (accept2 ⁺) (⟦ op ∷ [] ⟧ s )
  → (accept2 ⁺) (⟦ op ⟧ₛ s )
liftCondOperation2Program-from-simple accept2 op s a = a



liftCondOperation2Program-to : (accept1 accept2 : StackStatePred)
  (op : InstructionBasic)
  (correct : (s : StackState) → accept1 s → (accept2 ⁺) (⟦ op ⟧ₛ s ))
  (s : StackState)
  → accept1 s
  → (accept2 ⁺) (⟦ op ∷ [] ⟧ s )
liftCondOperation2Program-to accept1 accept2 op correct s a = correct s a


liftCondOperation2Program-from : (accept1 accept2 : StackStatePred)
   (op : InstructionBasic)
   (correct : (s : StackState) → (accept2 ⁺) (⟦ op ⟧ₛ s ) → accept1 s)
   (s : StackState)
   → (accept2 ⁺) (⟦ op ∷ [] ⟧ s ) → accept1 s
liftCondOperation2Program-from accept1 accept2 op correct s a = correct s a


emptyProgramCorrect-to : (accept1 : StackStatePred)
    (s : StackState) → accept1 s → (accept1 ⁺) (⟦ [] ⟧ s )
emptyProgramCorrect-to accept1 s a = a

emptyProgramCorrect-from : (accept1 : StackStatePred)
    (s : StackState) → (accept1 ⁺) (⟦ [] ⟧ s ) → accept1 s
emptyProgramCorrect-from accept1 s a = a


bindTransformerBack : (accept2 accept3 : StackStatePred)
     (f : StackState → Maybe StackState)
     (correct2 : (s : StackState) → (accept3 ⁺) (f s) → accept2 s)
     (s : Maybe StackState)
     → ((accept3 ⁺) (s >>= f )) → (accept2 ⁺) s
bindTransformerBack accept2 accept3 f correct2  (just s) a  = correct2 s a

bindTransformeraux : (accept2 accept3 : StackStatePred)
                        (f :  StackState → Maybe StackState)
                        (correct2 : (s : StackState) → accept2 s → (accept3 ⁺) (f s ))
                        → (s2 : Maybe StackState) →  ((accept2 ⁺) s2)
                        → (accept3 ⁺) (s2 >>= f)
bindTransformeraux accept2 accept3 f correct2  (just s) correct1 = correct2 s correct1


bindTransformer-toSingle : (accept1 accept2 accept3 : StackStatePred)
               (op : InstructionBasic)
               (p  : List InstructionBasic)
               (correct1 : (s : StackState) → accept1 s → (accept2 ⁺) (⟦ op ⟧ₛ s ))
               (correct2 : (s : StackState) → accept2 s → (accept3 ⁺) (⟦ p ⟧ s ))
               → (s : StackState)
               → accept1 s
               → (accept3 ⁺) (⟦ op ∷ p ⟧ s )
bindTransformer-toSingle accept1 accept2 accept3 op [] correct1 correct2 s a
                     = liftPredtransformerMaybe accept2 accept3 correct2 (⟦ op ⟧ₛ s) (correct1 s a)
bindTransformer-toSingle accept1 accept2 accept3 op ( p@(op₁ ∷ p₁) ) correct1 correct2 s a
                     = bindTransformeraux  accept2  accept3 ⟦ p  ⟧  correct2  (⟦ op ⟧ₛ  s) (correct1 s a)

bindTransformer-fromSingle : (accept1 accept2 accept3 : StackStatePred)
              (op : InstructionBasic)
              (p  : List InstructionBasic)
              (correct1 : (s : StackState) → (accept2 ⁺) (⟦ op ⟧ₛ s ) → accept1 s)
              (correct2 : (s : StackState) → (accept3 ⁺) (⟦ p ⟧ s ) → accept2 s) (s : StackState)
              → (accept3 ⁺) (⟦ op ∷ p ⟧ s ) → accept1 s
bindTransformer-fromSingle accept1 accept2 accept3 op [] correct1 correct2 s a
   = correct1 s (liftPredtransformerMaybe accept3 accept2 correct2 (⟦ op ⟧ₛ s) a)
bindTransformer-fromSingle accept1 accept2 accept3 op (p@(op₁ ∷ p₁)) correct1 correct2 s a
                    = correct1 s (bindTransformerBack accept2 accept3  ⟦ p ⟧  correct2 ( ⟦ op ⟧ₛ s)  a )



p++xSemLem :  (op : InstructionBasic)(s : Maybe StackState) (p : BitcoinScriptBasic)
        →  (⟦ p ⟧⁺ s  >>=  ⟦ op ⟧ₛ)
               ≡
           (⟦ p ++ (op ∷ []) ⟧⁺ s )
p++xSemLem op nothing s = refl
p++xSemLem op (just s) [] = refl
p++xSemLem op (just s) (op₁ ∷ []) = refl
p++xSemLem op (just s) (op₁ ∷ op₂ ∷ p) = p++xSemLem op (⟦ op₁ ⟧ₛ s) (op₂ ∷ p)

p++xSemLemb :  (op : InstructionBasic)(s : Maybe StackState) (p : BitcoinScriptBasic)
        →  (⟦ p ++ (op ∷ []) ⟧⁺ s )
               ≡
            (⟦ p ⟧⁺ s >>=  ⟦ op ⟧ₛ )
p++xSemLemb op nothing s = refl
p++xSemLemb op (just s) [] = refl
p++xSemLemb op (just s) (op₁ ∷ []) = refl
p++xSemLemb op (just s) (op₁ ∷ op₂ ∷ p) = p++xSemLemb op (⟦ op₁ ⟧ₛ s ) ( op₂ ∷ p )

p++x::qLem : (p1 p2 : BitcoinScriptBasic)(op : InstructionBasic) → p1 ++ op ∷' p2 ≡ (p1 ++ (op ∷ [])) ++ p2
p++x::qLem [] p2 op = refl
p++x::qLem (op₁ ∷ p1) p2 op = cong (λ p → op₁ ∷ p) (p++x::qLem p1 p2 op)

++[]lem : (p : BitcoinScriptBasic) → p ++ [] ≡ p
++[]lem [] = refl
++[]lem (op ∷ p) = cong (λ q → op ∷ q) (++[]lem p)

liftMaybeCompLemma : (f k : StackState → Maybe StackState)(s : Maybe StackState)
            → (s >>= λ s₁ → k s₁ >>= f ) ≡ ((s >>= k) >>= f)
liftMaybeCompLemma f k nothing = refl
liftMaybeCompLemma f k (just s) = refl

liftMaybeCompLemma2 : (f k : StackState → Maybe StackState)(s : Maybe StackState)
            → ((s >>= k) >>= f)  ≡ (s >>= λ s₁ → k s₁ >>= f )
liftMaybeCompLemma2 f k nothing = refl
liftMaybeCompLemma2 f k (just s) = refl


lemmaBindTransformerAux' : (p1 p2 : BitcoinScriptBasic)(s : Maybe  StackState)
    → ⟦ p2 ++ p1 ⟧⁺ s ≡ (⟦ p2 ⟧⁺ s >>= ⟦ p1 ⟧)
lemmaBindTransformerAux' [] p2 s = ⟦ p2 ++ [] ⟧⁺ s
                                        ≡⟨ cong (λ p → ⟦ p  ⟧⁺ s ) (++[]lem p2) ⟩
                                     ⟦ p2  ⟧⁺ s
                                        ≡⟨ liftJustEqLem2 (⟦ p2  ⟧⁺ s)  ⟩
                                     (⟦ p2 ⟧⁺ s >>= just )
                                     ∎

lemmaBindTransformerAux' (op ∷ []) p2 s = p++xSemLemb op s p2

lemmaBindTransformerAux' (op ∷ p1@(op₁ ∷ p1')) p2 s
        = ⟦ p2 ++ op ∷' p1 ⟧⁺ s
                ≡⟨ cong (λ p → ⟦ p ⟧⁺ s  ) (p++x::qLem p2 p1 op)  ⟩
             ⟦ (p2 ++ (op ∷ [])) ++ p1  ⟧⁺ s
                ≡⟨ lemmaBindTransformerAux'  p1 (p2 ++ (op ∷ [])) s  ⟩
             (⟦ p2 ++ (op ∷ []) ⟧⁺ s  >>= ⟦ p1 ⟧  )
                ≡⟨ cong ⟦ p1 ⟧⁺ (p++xSemLemb op s p2)  ⟩
             ((⟦ p2 ⟧⁺ s >>= ⟦ op ⟧ₛ   ) >>= ⟦ p1 ⟧  )
                ≡⟨ liftMaybeCompLemma2 ⟦ p1 ⟧  ⟦ op ⟧ₛ (⟦ p2 ⟧⁺ s )  ⟩
             ( ⟦ p2 ⟧⁺ s  >>= λ s₁ → ⟦ op ⟧ₛ s₁ >>= ⟦ p1 ⟧ )
                ≡⟨ refl  ⟩
            (⟦ p2 ⟧⁺ s  >>= ⟦ op ∷ p1 ⟧ )
             ∎


lemmaBindTransformer' : (p1 p2 : BitcoinScriptBasic)(s : StackState)
                       → ⟦ p2 ++ p1 ⟧ s ≡ (⟦ p2 ⟧ s >>= ⟦ p1 ⟧ )
lemmaBindTransformer' p1 p2 s = lemmaBindTransformerAux' p1 p2 (just s)




lemmaBindTransformerAux : (p1 p2 : BitcoinScriptBasic)(s : Maybe  StackState)
                          → ⟦ p2 ++ p1 ⟧⁺ s ≡ (⟦ p2 ⟧⁺ s >>= ⟦ p1 ⟧)
lemmaBindTransformerAux p1 [] s = lemmaBindTransformerAux' p1 [] s
lemmaBindTransformerAux p1 (op ∷ p2) s = lemmaBindTransformerAux' p1 (op ∷ p2) s

lemmaBindTransformer : (p1 p2 : BitcoinScriptBasic)(s : StackState)
                                → ⟦ p2 ++ p1 ⟧ s ≡ (⟦ p2 ⟧ s >>= ⟦ p1 ⟧ )
lemmaBindTransformer p₁ [] s = refl
lemmaBindTransformer [] (op ∷ []) s = liftJustIsIdLem (λ l → ⟦ op ⟧ₛ s ≡ l) (⟦ op ⟧ₛ s) refl
lemmaBindTransformer (op₁ ∷ p₁) (op ∷ []) s = refl
lemmaBindTransformer p₁ (op ∷ p₂@(op₁ ∷ p₂')) s = lemmaBindTransformerAux p₁ p₂ (⟦ op ⟧ₛ s)


lemmaBindTransformereq : (p2 : BitcoinScriptBasic)(s : StackState)
                               → ⟦ p2  ⟧ s ≡ (⟦ p2 ⟧ s >>= ⟦ [] ⟧)
lemmaBindTransformereq [] s = refl
lemmaBindTransformereq (op ∷ p₂) s = liftJustEqLem2 (⟦ op ∷ p₂ ⟧ s)

bindTransformer-toSequence : (accept1 accept2 accept3 : StackStatePred)
                               (p1 : BitcoinScriptBasic)
                               (p2  : BitcoinScriptBasic)
                               (correct1 : (s : StackState) → accept1 s → (accept2 ⁺) (⟦ p1 ⟧ s ))
                               (correct2 : (s : StackState) → accept2 s → (accept3 ⁺) (⟦ p2 ⟧ s ))
                               → (s : StackState) → accept1 s → (accept3 ⁺) (⟦ p1 ++ p2 ⟧ s )
bindTransformer-toSequence accept1 accept2 accept3 p1 p2 correct1 correct2 s a rewrite lemmaBindTransformer p2 p1 s
                                     = bindTransformeraux accept2 accept3 ⟦ p2 ⟧ correct2 ( ⟦ p1 ⟧ s  )(correct1 s a)

bindTransformer-fromSequence : (accept1 accept2 accept3 : StackStatePred)
                              (p1 : BitcoinScriptBasic)
                              (p2  : BitcoinScriptBasic)
                              (correct1 : (s : StackState) → (accept2 ⁺) (⟦ p1 ⟧ s ) → accept1 s)
                              (correct2 : (s : StackState) → (accept3 ⁺) (⟦ p2 ⟧ s ) → accept2 s)
                              → (s : StackState) → (accept3 ⁺) (⟦ p1 ++ p2 ⟧ s ) → accept1 s
bindTransformer-fromSequence accept1 accept2 accept3 p1 p2 correct1 correct2 s a   rewrite lemmaBindTransformer p2 p1 s
                                    = correct1 s (bindTransformerBack accept2 accept3 ⟦ p2 ⟧   correct2 (⟦ p1 ⟧ s) a)


bindTransformer-toSequenceeq : (accept1 accept2 accept3 : StackStatePred)
                               (p1 : BitcoinScriptBasic)
                               (correct1 : (s : StackState) → accept1 s → (accept2 ⁺) (⟦ p1 ⟧ s ))
                               (correct2 : (s : StackState) → accept2 s → (accept3 ⁺) (⟦ [] ⟧ s ))
                               → (s : StackState) → accept1 s → (accept3 ⁺) (⟦ p1 ⟧ s )
bindTransformer-toSequenceeq accept1 accept2 accept3 p1  correct1 correct2 s a rewrite lemmaBindTransformereq p1 s
                                   = bindTransformeraux accept2 accept3 ⟦ [] ⟧ correct2 ( ⟦ p1 ⟧ s  )(correct1 s a)


bindTransformer-fromSequenceeq : (accept1 accept2 accept3 : StackStatePred)
                              (p1 : BitcoinScriptBasic)
                              (correct1 : (s : StackState) → (accept2 ⁺) (⟦ p1 ⟧ s ) → accept1 s)
                              (correct2 : (s : StackState) → (accept3 ⁺) (⟦ [] ⟧ s ) → accept2 s)
                              → (s : StackState) → (accept3 ⁺) (⟦ p1  ⟧ s ) → accept1 s
bindTransformer-fromSequenceeq accept1 accept2 accept3 p1 correct1 correct2 s a  rewrite lemmaBindTransformereq p1 s
                                   = correct1 s (bindTransformerBack accept2 accept3 ⟦ [] ⟧   correct2 (⟦ p1 ⟧ s) a)
