open import basicBitcoinDataType

module verificationStackScripts.hoareTripleStackBasic (param : GlobalParameters) where

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
open import libraries.maybeLib
open import libraries.emptyLib


open import stack
open import stackPredicate
open import instructionBasic
open import hoareTripleStack param
open import verificationStackScripts.stackState
open import verificationStackScripts.sPredicate
open import verificationStackScripts.semanticsStackInstructions param
open import verificationStackScripts.stackSemanticsInstructionsBasic param
open import verificationStackScripts.stackVerificationLemmas param
open import verificationStackScripts.stackHoareTriple param


--------------------------------------------------------------------------
--   defines hoare triples for stack functions
--   and that their correspondence to the full hoare triples for nonif instructions
---------------------------------------------------------------------------------------


-- Hoare triple  with stack instructions
<_>stackb_<_> : StackPredicate → BitcoinScriptBasic → StackPredicate → Set
< φ >stackb prog < ψ > = < φ >gˢ (⟦ prog  ⟧ˢ ) < ψ >

-- Generalisation of <_>_<_>   by referring instead of Bitcoin Scripts
--                to functions of type StackState → Maybe StackState
-- Note that there is a version <_>gˢ_<_> in module hoareTripleStack for StackPredicate
--      which refers to StackPredicate instead of StackStatePred


record <_>g_<_>  (φ : StackStatePred) (stackfun : StackState → Maybe StackState)
                 (ψ : StackStatePred) : Set where
  constructor hoareTripleStackGenStackState
  field
    ==>stg : (s : StackState)
            → φ s
            → liftPred2Maybe ψ (stackfun s)
    <==stg : (s : StackState)
            → liftPred2Maybe ψ (stackfun s)
            → φ s
open <_>g_<_> public





-- Proof that the generic Hoare triple implies the standard one for an instruction
lemmaGenericHoareTripleImpliesHoareTriple : (instr : InstructionBasic)
                                            (φ ψ : StackStatePred)
                                            → < φ >ssgen ⟦ instr ⟧ₛ  < ψ >
                                            → < φ >ⁱᶠᶠ [ instr ] < ψ >
lemmaGenericHoareTripleImpliesHoareTriple instr φ ψ prog .==> = prog .==>g
lemmaGenericHoareTripleImpliesHoareTriple instr φ ψ prog .<== = prog .<==g


lemmaGenericHoareTripleImpliesHoareTriple'' : (prog : BitcoinScriptBasic)
                                            (φ ψ : StackStatePred)
                                            → < φ >ssgen ⟦ prog ⟧  < ψ >
                                            → < φ >ⁱᶠᶠ prog < ψ >
lemmaGenericHoareTripleImpliesHoareTriple'' prog φ ψ prog₁ .==> = prog₁ .==>g
lemmaGenericHoareTripleImpliesHoareTriple'' prog φ ψ prog₁ .<== = prog₁ .<==g



-- intermediate step towards showing that the
--   Hoare triple of a stack function implies
--   the Hoare triple of the instruction
lemmaNonIfInstrGenericCondImpliesTripleaux :
          (op : InstructionBasic)
          (φ ψ : StackStatePred)
          → < φ >ssgen stackTransform2StackStateTransform ⟦ [ op ] ⟧ˢ < ψ >
          → < φ >ssgen ⟦ op ⟧ₛ  < ψ >
lemmaNonIfInstrGenericCondImpliesTripleaux opEqual  φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opAdd  φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux (opPush x₁)  φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opSub  φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opVerify  φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opCheckSig  φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opEqualVerify  φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opDup  φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opDrop  φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opSwap  φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opHash  φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opCHECKLOCKTIMEVERIFY  φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opCheckSig3  φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opMultiSig  φ ψ x = x


lemmaNonIfInstrGenericCondImpliesHoareTriple :
          (op : InstructionBasic)
          (φ ψ : StackStatePred)
          → < φ >ssgen stackTransform2StackStateTransform ⟦ [ op ] ⟧ˢ < ψ >
          → < φ >ⁱᶠᶠ [ op ]  < ψ >
lemmaNonIfInstrGenericCondImpliesHoareTriple op φ ψ p
  = lemmaGenericHoareTripleImpliesHoareTriple op φ ψ
      (lemmaNonIfInstrGenericCondImpliesTripleaux op φ ψ p)



-- auxiliary function used for proving lemmaLift2StateCorrectnessStackFun=>
lemmaLift2StateCorrectnessStackFun=>aux : (ψ : StackPredicate)
                                          (funRes : Maybe Stack)
                                          (currentTime₁ : Time)
                                          (msg₁ : Msg)
                                          (p : liftPred2Maybe (ψ currentTime₁ msg₁) funRes)
                                          → ((stackPred2SPred ψ ) ⁺)
                                             (stackState2WithMaybe
                                               ⟨ currentTime₁ , msg₁ , funRes ⟩)
lemmaLift2StateCorrectnessStackFun=>aux ψ (just x) currentTime₁ msg₁ p = p


-- Stack correctness implies correctness of the hoare triple
--   here direction =>
lift2StateCorrectnessStackFun=> : (φ ψ : StackPredicate)
                                  (stackfun : StackTransformer)
                                  (stackCorrectness : (time : Time)(msg : Msg)(s : Stack)
                                  → φ time msg s → liftPred2Maybe (ψ time msg) (stackfun time msg s))
                                  (s : StackState)
                                  → stackPred2SPred φ s
                                  → ((stackPred2SPred ψ) ⁺)
                                                    (stackTransform2StackStateTransform stackfun s)
lift2StateCorrectnessStackFun=> φ ψ stackfun stackCorrectness ⟨ currentTime₁ , msg₁ , stack₁ ⟩  and3
      = lemmaLift2StateCorrectnessStackFun=>aux ψ  (stackfun currentTime₁ msg₁ stack₁) currentTime₁ msg₁
                   (stackCorrectness currentTime₁ msg₁ stack₁ and3)


lemmaLift2StateCorrectnessStackFun<=aux :
     (φ ψ : StackPredicate)
     (funRes : Maybe Stack)
     (currentTime₁ : Time)
     (msg₁ : Msg)
     (stack₁ : Stack)
     (p : ((λ s → ψ (currentTime s) (msg s) (stack s) ) ⁺)
            (exeTransformerDepIfStack'
             (liftStackToStateTransformerAux' funRes)
              ⟨ currentTime₁ , msg₁ , stack₁  ⟩))
     (q : liftPred2Maybe (ψ currentTime₁ msg₁) funRes → φ currentTime₁ msg₁ stack₁)
     → φ currentTime₁ msg₁ stack₁
lemmaLift2StateCorrectnessStackFun<=aux φ ψ (just x) currentTime₁ msg₁ stack₁ p q = q p


-- Stack correctness implies correctness of the hoare triple
--   here direction <=
lift2StateCorrectnessStackFun<= : (φ ψ : StackPredicate)
                                  (stackfun : StackTransformer)(stackCorrectness : (time : Time)(msg : Msg)(s : Stack)
                                  → liftPred2Maybe (ψ time msg) (stackfun time msg s) → φ time msg s)
                                  (s : StackState)
                                  → ((stackPred2SPred ψ) ⁺)
                                                    (stackTransform2StackStateTransform stackfun s)
                                  → stackPred2SPred φ s
lift2StateCorrectnessStackFun<=  φ ψ stackfun stackCorrectness ⟨ currentTime₁ , msg₁ , stack₁  ⟩ x
              = lemmaLift2StateCorrectnessStackFun<=aux φ ψ (stackfun currentTime₁ msg₁  stack₁)
                    currentTime₁ msg₁ stack₁ x  (stackCorrectness currentTime₁ msg₁ stack₁)



-- Correctness of the stack function implies correctness of the Hoare triple
--    here generic

lemmaHoareTripleStackPartToHoareTripleGeneric :
     (stackfun : StackTransformer)
     (φ ψ : StackPredicate)
     → < φ >gˢ stackfun  < ψ >
     → < stackPred2SPred φ >ssgen
        stackTransform2StackStateTransform  stackfun
        < stackPred2SPred ψ >
lemmaHoareTripleStackPartToHoareTripleGeneric stackfun  φ ψ
    (hoareTripleStackGen ==>stg₁ <==stg₁) .==>g s p
     = lift2StateCorrectnessStackFun=> φ  ψ  stackfun ==>stg₁ s p
lemmaHoareTripleStackPartToHoareTripleGeneric stackfun  φ ψ
    (hoareTripleStackGen ==>stg₁ <==stg₁) .<==g s p
     = lift2StateCorrectnessStackFun<= φ  ψ  stackfun <==stg₁ s p



-- Hoare triple correctness of the stack function of an instruction
-- implies correctness of the Hoare triple for that instruction

hoartTripleStackPartImpliesHoareTriple :
     (op : InstructionBasic)
     (φ ψ : StackPredicate)
     → < φ >stackb [ op ] < ψ >
     → < stackPred2SPred φ   >ⁱᶠᶠ [ op ]  <  stackPred2SPred ψ  >

hoartTripleStackPartImpliesHoareTriple op φ ψ x
   = lemmaGenericHoareTripleImpliesHoareTriple op
      (stackPred2SPred φ)
      (stackPred2SPred ψ)
      (lemmaNonIfInstrGenericCondImpliesTripleaux op
         (stackPred2SPred φ)
        (stackPred2SPred ψ)
        (lemmaHoareTripleStackPartToHoareTripleGeneric
           ⟦ [ op ] ⟧ˢ  φ ψ x))
