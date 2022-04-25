module verificationStackScripts.stackState where

open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  hiding (_≤_)
open import Data.Empty
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

open import basicBitcoinDataType
open import stack


record StackState  : Set  where
       constructor ⟨_,_,_⟩
       field  currentTime :  Time  -- current time, i.e. time when the the smart contract is executed
              msg         :  Msg
              stack       :  Stack


open StackState public


record StackStateWithMaybe  : Set  where
       constructor ⟨_,_,_⟩
       field
         currentTime : Time  -- current time, i.e. time when the
                             -- the smart contract is executed
         msg : Msg
         maybeStack : Maybe Stack

open StackStateWithMaybe public


stackState2WithMaybe : StackStateWithMaybe → Maybe StackState
stackState2WithMaybe ⟨ currentTime₁ , msg₁ , just x  ⟩ = just ⟨ currentTime₁ , msg₁ , x  ⟩
stackState2WithMaybe ⟨ currentTime₁ , msg₁ , nothing ⟩ = nothing




mutual

  liftStackToStateTransformerAux' : Maybe Stack → StackState → StackStateWithMaybe
  liftStackToStateTransformerAux' maybest ⟨ currentTime₁ , msg₁ , stack₁  ⟩ = ⟨ currentTime₁ , msg₁ , maybest  ⟩




exeTransformerDepIfStack' : ( StackState → StackStateWithMaybe ) →  StackState → Maybe StackState
exeTransformerDepIfStack' f s = stackState2WithMaybe (f s)


stackTransform2StackStateTransform : StackTransformer  → StackState → Maybe StackState
stackTransform2StackStateTransform f s
     = stackState2WithMaybe ((liftStackToStateTransformerAux' (f (s .currentTime) (s .msg) (s .stack))) s )


liftStackToStackStateTransformer' : (Stack → Maybe Stack)  → StackState → Maybe StackState
liftStackToStackStateTransformer' f = stackTransform2StackStateTransform (λ time msg → f)


liftTimeStackToStateTransformer' : (Time → Stack → Maybe Stack)  → StackState → Maybe StackState
liftTimeStackToStateTransformer' f = stackTransform2StackStateTransform (λ time msg → f time)

liftMsgStackToStateTransformer' : (Msg → Stack → Maybe Stack)  → StackState → Maybe StackState
liftMsgStackToStateTransformer' f = stackTransform2StackStateTransform (λ time msg → f msg)




msgToMStackToIfStackToMState : Time → Msg  → Maybe Stack → Maybe StackState
msgToMStackToIfStackToMState time msg nothing = nothing
msgToMStackToIfStackToMState time msg (just x) = just ⟨ time , msg , x ⟩


liftStackFun2StackState : (Time → Msg → Stack → Maybe Stack) → StackState → Maybe StackState
liftStackFun2StackState f ⟨ currentTime₁ , msg₁ , stack₁ ⟩ =
    stackState2WithMaybe ⟨ currentTime₁ , msg₁ ,(f currentTime₁  msg₁  stack₁) ⟩

