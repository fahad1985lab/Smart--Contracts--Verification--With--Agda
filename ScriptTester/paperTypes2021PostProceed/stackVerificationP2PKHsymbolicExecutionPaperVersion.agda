open import basicBitcoinDataType

module paperTypes2021PostProceed.stackVerificationP2PKHsymbolicExecutionPaperVersion (param : GlobalParameters)  where

open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Sum
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
open import Data.List.NonEmpty hiding (head ; [_] )
open import Data.Maybe
open import Relation.Nullary

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality


--our libraries
open import libraries.listLib
open import libraries.equalityLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.emptyLib
open import libraries.andLib
open import libraries.maybeLib

open import stack
open import stackPredicate
open import semanticBasicOperations param
open import hoareTripleStack param
open import instruction
open import verificationStackScripts.stackState
open import verificationStackScripts.sPredicate
open import verificationStackScripts.stackHoareTriple param
open import verificationStackScripts.stackVerificationLemmas param
open import verificationStackScripts.stackSemanticsInstructionsBasic param
open import verificationStackScripts.semanticsStackInstructions param
open import verificationStackScripts.stackVerificationP2PKH param
open import verificationStackScripts.stackVerificationP2PKHindexed param

-------------------------------------------------------------
--   This file explores the symoblic execution of the P2PKH program
--     in order to determine the case distinction
--     and extract a program from it
--
--   This is done by postulating parameters and applying ⟦ scriptP2PKHᵇ pbkh ⟧ˢ
--     to parameters
--------------------------------------------------------------------------------

private
  postulate time₁ : Time
  postulate msg₁ : Msg
  postulate stack₁ : Stack
  postulate pbkh : ℕ
  postulate pbk : ℕ
  postulate x₁ : ℕ
  postulate sig₁ : ℕ


{- We first create a symbolic execution of the scriptP2PKHᵇ pbkh to see what kind
   of case distinction happens -}

check = scriptP2PKHᵇ

testP2PKHscript : Maybe Stack
testP2PKHscript =
 ⟦ scriptP2PKHᵇ pbkh ⟧ˢ time₁ msg₁ stack₁




--⟦ scriptP2PKHᵇ pbkh ⟧ˢ time₁ msg₁ stack

{- evaluation gives

executeStackDup stack₁ >>=
(λ stack₂ →
   executeOpHash stack₂ >>=
   (λ stack₃ →
      executeStackEquality (pbkh ∷ stack₃) >>=
      (λ stack₄ →
         executeStackVerify stack₄ >>=
         (λ stack₅ → executeStackCheckSig msg₁ stack₅))))

Improved layout
executeStackDup stack₁ >>= (λ stack₂ →  executeOpHash stack₂ >>=
   (λ stack₃ →  executeStackEquality (pbkh ∷ stack₃) >>=
   (λ stack₄ →  executeStackVerify stack₄ >>=
   (λ stack₅ → executeStackCheckSig msg₁ stack₅))))

-}

-- We define a term giving the result of the evaluation

testP2PKHscript2 : Maybe Stack
testP2PKHscript2 =
 executeStackDup stack₁                >>=  λ stack₂ →  executeOpHash stack₂       >>= λ stack₃ →
 executeStackEquality (pbkh ∷ stack₃)  >>=  λ stack₄ →  executeStackVerify stack₄  >>= λ stack₅ →
 executeStackCheckSig msg₁ stack₅


testP2PKHscript2UsingMoreSpace =
 executeStackDup stack₁                             >>=
 λ stack₂ →  executeOpHash stack₂                   >>=
 λ stack₃ →  executeStackEquality (pbkh ∷ stack₃)   >>=
 λ stack₄ →  executeStackVerify stack₄              >>=
 λ stack₅ →  executeStackCheckSig msg₁ stack₅



testP2PKHscript2UsingMoreSpaceUsingDo =
 do  stack₂ ← executeStackDup stack₁
     stack₃ ← executeOpHash stack₂
     stack₄ ← executeStackEquality (pbkh ∷ stack₃)
     stack₅ ← executeStackVerify stack₄
     executeStackCheckSig msg₁ stack₅



{- in imperative programming we would write

   stack₂ := executeStackDup stack₁;
   stack₃ := executeOpHash stack₂;
   stack₄ := executeStackEquality (pbkh ∷ stack₃);
   stack₅ := executeStackVerify stack₄;
   executeStackCheckSig msg₁ stack₅;

-}


{-
If we execute the first line
(executeStackDup stack₁)

we see it will give
nothing if stack₁ = []
just something if stack₁ is nonempty

So let's check what happens if stack₁ = []
-}


testP2PKHscriptEmpty : Maybe Stack
testP2PKHscriptEmpty =
 ⟦ scriptP2PKHᵇ pbkh ⟧ˢ time₁ msg₁ []




{- if we evaluate testP2PKHscriptEmpty we get:

nothing

So now get the first (trivial) theorem
(without the postulated parameters)
-}



stackfunP2PKHemptyIsNothing : (pubKeyHash : ℕ)(time₁ : Time)(msg₁ : Msg)
                              → ⟦ scriptP2PKHᵇ pubKeyHash ⟧ˢ time₁ msg₁ [] ≡ nothing
stackfunP2PKHemptyIsNothing pubKeyHash time₁ msg₁ = refl




{- Now we look at what happens if the stack is non empty

lets a test for symbolic execution -}


teststackfunP2PKHNonEmptyStack :  Maybe Stack
teststackfunP2PKHNonEmptyStack =
  ⟦ scriptP2PKHᵇ pbkh ⟧ˢ time₁ msg₁ (pbk ∷ stack₁)

{- If we evaluate teststackfunP2PKHNonEmptyStack we get
executeStackVerify (compareNaturals pbkh (param .hash pbk) ∷ pbk ∷ stack₁)
>>= (λ stack₂ → executeStackCheckSig msg₁ stack₂)
-}

stackfunP2PKHNonEmptyStackNormalForm :  Maybe Stack
stackfunP2PKHNonEmptyStackNormalForm =
 executeStackVerify (compareNaturals pbkh (hashFun pbk) ∷ pbk ∷ stack₁) >>=
 executeStackCheckSig msg₁


stackfunP2PKHNonEmptyStackNormalFormDo :  Maybe Stack
stackfunP2PKHNonEmptyStackNormalFormDo =
 do   stack₅ ← executeStackVerify (compareNaturals pbkh (hashFun pbk) ∷ pbk ∷ stack₁)
      executeStackCheckSig msg₁ stack₅





stackfunP2PKHNonEmptyStackNormalFormFirstPart :  Maybe Stack
stackfunP2PKHNonEmptyStackNormalFormFirstPart =
 executeStackVerify (compareNaturals pbkh (hashFun pbk) ∷ pbk ∷ stack₁)


stackfunP2PKHNonEmptyStackNormalFormFirstPartZoomedIn :  ℕ
stackfunP2PKHNonEmptyStackNormalFormFirstPartZoomedIn =
 compareNaturals pbkh (hashFun pbk)





{-
We see that

(λ stack₂ → executeStackCheckSig msg₁ stack₂) = executeStackCheckSig msg₁

and can therefore use

executeStackVerify (compareNaturals pbkh (param .hash pbk) ∷ pbk ∷ stack₁)
>>= executeStackCheckSig msg₁

 -}




stackfunP2PKHNonEmptyStack : (pubKeyHash : ℕ)(msg₁ : Msg)(pbk : ℕ)(stack₂ : Stack) → Maybe Stack
stackfunP2PKHNonEmptyStack pubKeyHash msg₁ pbk stack₂
              = executeStackVerify (compareNaturals pubKeyHash (hashFun pbk) ∷ pbk ∷ stack₂)
                 >>= executeStackCheckSig msg₁




-- and check that this is correct

stackfunP2PKHemptyNonEmptyStackCorrect : (pubKeyHash : ℕ)(time₁ : Time)(msg₁ : Msg)(pbk : ℕ)(stack₂ : Stack)
        → ⟦ scriptP2PKHᵇ pubKeyHash  ⟧ˢ time₁ msg₁ (pbk ∷ stack₂) ≡ stackfunP2PKHNonEmptyStack pubKeyHash msg₁  pbk stack₂
stackfunP2PKHemptyNonEmptyStackCorrect pubKeyHash time₁ msg₁ pbk stack₂ = refl



{- We see now the case distinction depends on
   compres := compareNaturals pbkh (hashFun pbk)

since

executeStackVerify    (compres ∷  pbk ∷ stack₁)

will depend on whether compres is 0 or  suc x'

so we abstract from

compres = compareNaturals pubKeyHash (hashFun pbk)

-}

-- This function will be repeated in stackVerificationP2PKHextractedProgram.agda
-- and therefore is kept private in this section in order to avoid a conflict
-- \stackVerificationPtoPKHsymbolicExecutionabstract

p2PKHNonEmptyStackAbstr' : (msg₁ : Msg)(pbk : ℕ)(stack₁ : Stack)(cmp : ℕ) → Maybe Stack
p2PKHNonEmptyStackAbstr' msg₁ pbk stack₁ cmp =  executeStackVerify (cmp ∷  pbk ∷ stack₁) >>=
                                                executeStackCheckSig msg₁


abstrFun : (stack₁ : Stack)(cmp : ℕ) → Maybe Stack
abstrFun stack₁ cmp =  do  stack₅ ← executeStackVerify (cmp ∷  pbk ∷ stack₁)
                           executeStackCheckSig msg₁ stack₅




stackfunP2PKHNonEmptyStackNormalFormUsingAbstractedFun : Maybe Stack
stackfunP2PKHNonEmptyStackNormalFormUsingAbstractedFun =
  abstrFun stack₁ (compareNaturals pbkh (hashFun pbk))


stackfunP2PKHNonEmptyStackNormalFormUsingAbstractedFunTest :
    stackfunP2PKHNonEmptyStackNormalForm ≡ stackfunP2PKHNonEmptyStackNormalFormUsingAbstractedFun
stackfunP2PKHNonEmptyStackNormalFormUsingAbstractedFunTest  = refl

-- and we show that this is the right function


-- This function will be repeated in stackVerificationP2PKHextractedProgram.agda
-- and therefore is kept private in this section in order to avoid a conflict
private
  stackfunP2PKHNonEmptyStackAbstractedCor :  (pubKeyHash : ℕ)(time₁ : Time)(msg₁ : Msg)(pbk : ℕ)(stack₂ : Stack)
                  → ⟦ scriptP2PKHᵇ pubKeyHash ⟧ˢ time₁ msg₁ (pbk ∷ stack₂)
                     ≡ p2PKHNonEmptyStackAbstr'  msg₁ pbk stack₂
                             (compareNaturals pubKeyHash (hashFun pbk))
  stackfunP2PKHNonEmptyStackAbstractedCor pubKeyHash time₁ msg₁ pbk stack₂ = refl


{- Now we investigate what  p2PKHNonEmptyStackAbstr'
When looking at it and see that

 p2PKHNonEmptyStackAbstr' msg₁ pbk stack₂ cmp

will execute
executeStackVerify (cmp ∷  pbk ∷ stack₂)
which will in turn make a case disctintion on whether cmp is 0 or  not zero

(that corresponds to what the original function does because it makes this comparison
   compareNaturals pubKeyHash (hashFun pbk)
  which checks  whether the pbk provided  by the user hashes to the pubKeyHash of the locking script
    if it  is 0 it should fail, and if it is 1 it should succeed.

So lets make the test
-}

testStackfunP2PKHNonEmptyStackAbstractedCompre0 : Maybe Stack
testStackfunP2PKHNonEmptyStackAbstractedCompre0 = p2PKHNonEmptyStackAbstr' msg₁ pbk stack₁ 0

{- if we evaluate testStackfunP2PKHNonEmptyStackAbstractedCompre0 we get

nothing
-}

-- we evaluate now
abstrFunZeroCase : Maybe Stack
abstrFunZeroCase = abstrFun stack₁ 0



-- We  show now this is always the case



-- This function will be repeated in stackVerificationP2PKHextractedProgram.agda
-- and therefore is kept private in this section in order to avoid a conflict
private
  stackfunP2PKHNonEmptyStackAbstractedCorCompr0IsNothing : (msg₁ : Msg)(pbk : ℕ)(stack₂ : Stack)
        →  p2PKHNonEmptyStackAbstr' msg₁ pbk stack₂ 0 ≡ nothing
  stackfunP2PKHNonEmptyStackAbstractedCorCompr0IsNothing msg₁ pbk stack₂ = refl


{- Now we look at what happens  if the value is non zero -}


testStackfunP2PKHNonEmptyStackAbstractedCompreSucCase : Maybe Stack
testStackfunP2PKHNonEmptyStackAbstractedCompreSucCase = p2PKHNonEmptyStackAbstr' msg₁ pbk stack₁ (suc x₁)




-- we evaluate now
abstrFunSucCase : Maybe Stack
abstrFunSucCase = abstrFun stack₁ (suc x₁)


-- we obtain

abstrFunSucCaseNormal : Maybe Stack
abstrFunSucCaseNormal =
  executeStackCheckSig msg₁ (pbk ∷ stack₁)


-- executeStackCheckSig msg₁ (pbk ∷ stack₁)



{- if we evalute
     testStackfunP2PKHNonEmptyStackAbstractedCompreSucCase
    we get

executeStackCheckSig msg₁ (pbk ∷ stack₁)


This corresponds to the situation where
the original stack₁ was non empty, and the comparision of the pbk with the pbkhash
got a result > 0



If we look at
executeStackCheckSig

we see that it gives nothing when the stack has height < 2
and otherwise does something,

so we can  make a case distinction on whether in

p2PKHNonEmptyStackAbstr' msg₁ pbk stack₁ x

stack₁ is [] or nonempty

So lets look at the easy case []

    -}


-- we evaluate now
abstrFunSucCaseEmpty : Maybe Stack
abstrFunSucCaseEmpty = abstrFun [] (suc x₁)


-- and obtain nothing
abstrFunSucCaseEmptyCheck :  abstrFunSucCaseEmpty ≡ nothing
abstrFunSucCaseEmptyCheck = refl

-- we evaluate now
abstrFunSucCaseNonEmpty : Maybe Stack
abstrFunSucCaseNonEmpty =
  abstrFun (sig₁ ∷ stack₁) (suc x₁)



abstrFunSucCaseNonEmptyNormal : Maybe Stack
abstrFunSucCaseNonEmptyNormal =
  just (boolToNat (isSigned msg₁ sig₁ pbk) ∷ stack₁)


abstrFunSucCaseNonEmptyCheck : abstrFunSucCaseNonEmpty ≡ abstrFunSucCaseNonEmptyNormal
abstrFunSucCaseNonEmptyCheck = refl


testStackfunP2PKHNonEmptyStackAbstractedCompreSucEmpty : Maybe Stack
testStackfunP2PKHNonEmptyStackAbstractedCompreSucEmpty =
                           p2PKHNonEmptyStackAbstr' msg₁ pbk [] (suc x₁)


{- if we evaluate testStackfunP2PKHNonEmptyStackAbstractedCompreSucEmpty we get  result

nothing

we check that this always holds
-}


stackfunP2PKHNonEmptyStackAbstractedCorComprSucStackEmpty : (msg₁ : Msg)(pbk : ℕ)(x : ℕ)
             → p2PKHNonEmptyStackAbstr' msg₁ pbk [] (suc x) ≡ nothing
stackfunP2PKHNonEmptyStackAbstractedCorComprSucStackEmpty msg₁ pbk x  = refl

{-  Intermezzo: we can see that stackfunP2PKHNonEmptyStackAbstractedCorComprSucStackEmpty returns always nothing if the stack is empty
   independent of the result

But this result is not really needed 
   -}

-- This function will be repeated in stackVerificationP2PKHextractedProgram.agda
-- and therefore is kept private in this section in order to avoid a conflict
private
  stackfunP2PKHNonEmptyStackAbstractedCorEmptysNothing : (msg₁ : Msg)(pbk : ℕ)(x : ℕ)
        →  p2PKHNonEmptyStackAbstr' msg₁ pbk [] x ≡ nothing

  stackfunP2PKHNonEmptyStackAbstractedCorEmptysNothing msg₁ pbk₁ zero = refl
  stackfunP2PKHNonEmptyStackAbstractedCorEmptysNothing msg₁ pbk₁ (suc x) = refl

{- Now we look at what happens if we have non empty stack₁ and comparision > 0
-}

{- if we evaluate stackfunP2PKHNonEmptyStackAbstractedCorEmptysNothing we get

just (boolToNat (isSigned  msg₁ sig₁ pbk) ∷ stack₁)



and we show that this is the case

-}


testStackfunP2PKHNonEmptyStackAbstractedCompreSucNonEmpty : Maybe Stack
testStackfunP2PKHNonEmptyStackAbstractedCompreSucNonEmpty = p2PKHNonEmptyStackAbstr' msg₁ pbk (sig₁  ∷ stack₁) (suc x₁)



stackfunP2PKHNonEmptyStackAbstractedCorComprSucStackNonEmptyCor :
       (msg₁ : Msg)(pbk : ℕ)(x : ℕ)(sig₁ : ℕ)(stack₂ : Stack)
       → p2PKHNonEmptyStackAbstr' msg₁ pbk (sig₁  ∷ stack₂) (suc x)
          ≡  just (boolToNat (isSigned  msg₁ sig₁ pbk) ∷ stack₂)
stackfunP2PKHNonEmptyStackAbstractedCorComprSucStackNonEmptyCor msg₂ pbk₁ sig₁ x stack₃ = refl



{- this theorem is not needed but an interesting observation -}

stackfunP2PKHemptySingleStackIsNothing : (pubKeyHash : ℕ)(time₁ : Time)(msg₁ : Msg)(pbk : ℕ)
        → ⟦ scriptP2PKHᵇ pubKeyHash ⟧ˢ time₁ msg₁ (pbk ∷ []) ≡ nothing
stackfunP2PKHemptySingleStackIsNothing  pubKeyHash time₁ msg₁ pbk
  =  ⟦ scriptP2PKHᵇ pubKeyHash ⟧ˢ time₁ msg₁ (pbk ∷ [])
               ≡⟨ stackfunP2PKHNonEmptyStackAbstractedCor pubKeyHash time₁ msg₁ pbk []   ⟩
     p2PKHNonEmptyStackAbstr' msg₁ pbk [] (compareNaturals pubKeyHash (hashFun pbk))
               ≡⟨ stackfunP2PKHNonEmptyStackAbstractedCorEmptysNothing msg₁ pbk (compareNaturals pubKeyHash (hashFun pbk))   ⟩
     nothing
     ∎

abstrFunSucCaseNonEmptyNormalSubTerm1 : ℕ
abstrFunSucCaseNonEmptyNormalSubTerm1 =
  boolToNat (isSigned msg₁ sig₁ pbk)


abstrFunSucCaseNonEmptyNormalSubTerm2 : Bool
abstrFunSucCaseNonEmptyNormalSubTerm2 =
  isSigned msg₁ sig₁ pbk
