open import basicBitcoinDataType

module verificationStackScripts.stackVerificationLemmasPart2 (param : GlobalParameters) where


open import Data.List.Base hiding (_++_ )
open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_  )
open import Data.Sum
open import Data.Unit  
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
open import libraries.maybeLib

open import stack
open import stackPredicate
open import semanticBasicOperations param
open import instructionBasic
open import verificationMultiSig param
open import hoareTripleStack param
open import verificationStackScripts.semanticsStackInstructions param
open import verificationStackScripts.stackVerificationLemmas param
open import verificationStackScripts.stackHoareTriple param
open import verificationStackScripts.sPredicate
open import verificationStackScripts.hoareTripleStackBasic param
open import verificationStackScripts.stackState
open import verificationStackScripts.stackSemanticsInstructionsBasic param




lemmaStackSemIsSemantics : (op : InstructionBasic)
                          → ⟦ op ⟧ₛ  ≡ stackTransform2StackStateTransform ⟦ [ op ] ⟧ˢ
lemmaStackSemIsSemantics opEqual = refl
lemmaStackSemIsSemantics opAdd  = refl
lemmaStackSemIsSemantics (opPush x)  =  refl
lemmaStackSemIsSemantics opSub  = refl
lemmaStackSemIsSemantics opVerify  = refl
lemmaStackSemIsSemantics opCheckSig  = refl
lemmaStackSemIsSemantics opEqualVerify  = refl
lemmaStackSemIsSemantics opDup  = refl
lemmaStackSemIsSemantics opDrop  = refl
lemmaStackSemIsSemantics opSwap  = refl
lemmaStackSemIsSemantics opHash  = refl
lemmaStackSemIsSemantics opCHECKLOCKTIMEVERIFY  = refl
lemmaStackSemIsSemantics opCheckSig3  = refl
lemmaStackSemIsSemantics opMultiSig  = refl



lemmaStackSemIsSemScriptaux2 : (g' : Time → Msg → Stack → Maybe Stack)
                             (st : StackState) (mst : Maybe Stack)
   → (exeTransformerDepIfStack'  (liftStackToStateTransformerAux' mst )  st
      >>=
        (λ s →  exeTransformerDepIfStack'
           (liftStackToStateTransformerAux'
            (g' (s .currentTime) (s .msg) (s .stack))) s))

      ≡
      exeTransformerDepIfStack'  (liftStackToStateTransformerAux'
             (mst >>= (g' (st .currentTime) (st .msg)) )) st
lemmaStackSemIsSemScriptaux2 g' ⟨ currentTime₁ , msg₁ , stack₁  ⟩ (just x) = refl
lemmaStackSemIsSemScriptaux2 g' ⟨ currentTime₁ , msg₁ , stack₁ ⟩ nothing = refl


lemmaStackSemIsSemScript : (prog : BitcoinScriptBasic)
                           (stackstate : StackState)
                          → ⟦ prog ⟧ stackstate  ≡ stackTransform2StackStateTransform ⟦ prog ⟧ˢ stackstate
lemmaStackSemIsSemScript [] ⟨ currentTime₁ , msg₁ , stack₁ ⟩ = refl
lemmaStackSemIsSemScript (op ∷ []) ⟨ currentTime₁ , msg₁ , stack₁ ⟩ rewrite  lemmaStackSemIsSemantics op = refl
lemmaStackSemIsSemScript (op ∷ rest@(op₁ ∷ prog)) ⟨ currentTime₁ , msg₁ , stack₁ ⟩ =
     (⟦ op ⟧ₛ ⟨ currentTime₁ , msg₁ , stack₁ ⟩ >>= ⟦ rest ⟧ )
          ≡⟨ cong (λ x → (x ⟨ currentTime₁ , msg₁ , stack₁ ⟩ >>= ⟦ rest ⟧))
                  (lemmaStackSemIsSemantics op )  ⟩
       (stackTransform2StackStateTransform ⟦ op ⟧ₛˢ  ⟨ currentTime₁ , msg₁ , stack₁ ⟩
        >>= ⟦ rest ⟧)

          ≡⟨ lemmaEqualLift2Maybe  ⟦ rest ⟧  (stackTransform2StackStateTransform ⟦ rest ⟧ˢ )
            (lemmaStackSemIsSemScript rest )
            ((stackTransform2StackStateTransform ⟦ op ⟧ₛˢ  ⟨ currentTime₁ , msg₁ , stack₁  ⟩)) ⟩
       (stackTransform2StackStateTransform ⟦ op ⟧ₛˢ  ⟨ currentTime₁ , msg₁ , stack₁  ⟩ >>= stackTransform2StackStateTransform ⟦ rest ⟧ˢ)
                ≡⟨ lemmaStackSemIsSemScriptaux2 ⟦ op₁ ∷ prog ⟧ˢ ⟨ currentTime₁ , msg₁ , stack₁  ⟩
                   (⟦ op ⟧ₛˢ currentTime₁ msg₁ stack₁) ⟩
        stackState2WithMaybe
      ⟨ currentTime₁ , msg₁ ,
      (⟦ op ⟧ₛˢ currentTime₁ msg₁ stack₁ >>= ⟦ rest ⟧ˢ currentTime₁ msg₁)

      ⟩
    ∎





lemmaGenericHoareTripleImpliesHoareTripleProg : (prog : BitcoinScriptBasic)
                                            (φ ψ : StackStatePred)
                                            → < φ >ssgen ⟦ prog ⟧  < ψ >
                                            → < φ >ⁱᶠᶠ prog < ψ >
lemmaGenericHoareTripleImpliesHoareTripleProg prog φ ψ (hoareTripleSSGen ==>g₁ <==g₁) .==> = ==>g₁
lemmaGenericHoareTripleImpliesHoareTripleProg prog φ ψ (hoareTripleSSGen ==>g₁ <==g₁) .<== = <==g₁

lemmaNonIfInstrGenericCondImpliesTripleauxProg :
          (prog : BitcoinScriptBasic)
          (φ ψ : StackStatePred)
          → < φ >ssgen stackTransform2StackStateTransform ⟦ prog ⟧ˢ < ψ >
          → < φ >ssgen ⟦ prog ⟧ < ψ >
lemmaNonIfInstrGenericCondImpliesTripleauxProg prog  φ ψ x  =
    lemmaTransferHoareTripleGen φ ψ
      (stackTransform2StackStateTransform ⟦ prog ⟧ˢ) ⟦ prog ⟧
     ( (λ s → sym (lemmaStackSemIsSemScript prog  s))) x





hoareTripleStack2HoareTriple :
     (prog : BitcoinScriptBasic)
     (φ ψ : StackPredicate)
     → < φ >stackb prog < ψ >
     → < stackPred2SPred φ  >ⁱᶠᶠ prog < stackPred2SPred ψ   >
hoareTripleStack2HoareTriple prog φ ψ x
  = lemmaGenericHoareTripleImpliesHoareTripleProg prog (stackPred2SPred φ) (stackPred2SPred ψ)
  (lemmaNonIfInstrGenericCondImpliesTripleauxProg prog (stackPred2SPred φ) (stackPred2SPred ψ)
   (lemmaHoareTripleStackPartToHoareTripleGeneric ⟦ prog ⟧ˢ
    φ ψ x))




lemmaTransferHoareTripleStack : (φ ψ : StackPredicate)
                              (f g : Time → Msg → Stack → Maybe Stack)
                              (p : (t : Time)(m : Msg)(s : Stack) → f t m s  ≡ g t m s)
                              → < φ >gˢ f  < ψ >
                              → < φ >gˢ g < ψ >
lemmaTransferHoareTripleStack φ ψ f g p (hoareTripleStackGen ==>stg₁ <==stg₁) .==>stg time msg₁ s x
        = transfer (liftPred2Maybe (ψ time msg₁)) (p time msg₁ s) (==>stg₁ time msg₁ s x)
lemmaTransferHoareTripleStack φ ψ f g p (hoareTripleStackGen ==>stg₁ <==stg₁) .<==stg time msg₁ s x
         = <==stg₁ time msg₁ s (transfer (liftPred2Maybe (ψ time msg₁)) (sym (p time msg₁ s)) x)
