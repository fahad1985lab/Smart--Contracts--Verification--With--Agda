open import basicBitcoinDataType

module verificationStackScripts.stackVerificationP2PKHsymbolicExecution (param : GlobalParameters)  where



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
open import libraries.miscLib
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

--test P2PKHscript
testP2PKHscript : Maybe Stack
testP2PKHscript = ⟦ scriptP2PKHᵇ pbkh ⟧ˢ time₁ msg₁ stack₁



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



-- old version was

lift2Maybe
(λ stack₂ →
   lift2Maybe
   (λ stack₃ →
      lift2Maybe
      (λ stack₄ →
         lift2Maybe (λ stack₅ → executeStackCheckSig msg₁ stack₅)
         (executeStackVerify stack₄))
      (executeStackEquality (pbkh ∷ stack₃)))
   (executeOpHash stack₂))
(executeStackDup stack₁)

-}

-- We define a term giving the result of the evaluation

testP2PKHscript2 : Maybe Stack
testP2PKHscript2 = executeStackDup stack₁ >>= λ stack₂ →  executeOpHash stack₂ >>= λ stack₃ →
                   executeStackEquality (pbkh ∷ stack₃) >>=   λ stack₄ →  executeStackVerify stack₄ >>= λ stack₅ →
                   executeStackCheckSig msg₁ stack₅



{-
If we execute the first line
(executeStackDup stack₁)

we see it will give
nothing if stack₁ = []
just something if stack₁ is nonempty

So let's check what happens if stack₁ = []
-}


--Empty
testP2PKHscriptEmpty : Maybe Stack
testP2PKHscriptEmpty = ⟦ scriptP2PKHᵇ pbkh ⟧ˢ time₁ msg₁ []



--⟦ scriptP2PKHᵇ pbkh ⟧ˢ time₁ msg₁ []



{- if we evaluate it we get:

nothing

So now get the first (trivial) theorem
(without the postulated parameters)
-}


--nothing
stackfunP2PKHemptyIsNothing : (pubKeyHash : ℕ)(time₁ : Time)(msg₁ : Msg)
                              → ⟦ scriptP2PKHᵇ pubKeyHash ⟧ˢ time₁ msg₁ [] ≡ nothing
stackfunP2PKHemptyIsNothing pubKeyHash time₁ msg₁ = refl




{- Now we look at what happens if the stack is non empty

lets a test for symbolic execution -}


--nonestack
teststackfunP2PKHNonEmptyStack :  Maybe Stack
teststackfunP2PKHNonEmptyStack =  ⟦ scriptP2PKHᵇ pbkh ⟧ˢ time₁ msg₁ (pbk ∷ stack₁)


{- If we compute it we get
executeStackVerify (compareNaturals pbkh (param .hash pbk) ∷ pbk ∷ stack₁)
>>= (λ stack₂ → executeStackCheckSig msg₁ stack₂)

-- older version was
lift2Maybe (λ stack₂ → executeStackCheckSig msg₁ stack₂)
(executeStackVerify
 (compareNaturals pbkh (hashFun pbk) ∷ pbk ∷ stack₁))



We see that

(λ stack₂ → executeStackCheckSig msg₁ stack₂) = executeStackCheckSig msg₁

and can therefore use

executeStackVerify (compareNaturals pbkh (param .hash pbk) ∷ pbk ∷ stack₁)
>>= executeStackCheckSig msg₁

-- older version
lift2Maybe (executeStackCheckSig msg₁)
(executeStackVerify
 (compareNaturals pbkh (hashFun pbk) ∷ pbk ∷ stack₁))

 -}



--stack empty
stackfunP2PKHNonEmptyStack : (pubKeyHash : ℕ)(msg₁ : Msg)(pbk : ℕ)(stack₂ : Stack) → Maybe Stack
stackfunP2PKHNonEmptyStack pubKeyHash msg₁ pbk stack₂
              = executeStackVerify (compareNaturals pubKeyHash (hashFun pbk) ∷ pbk ∷ stack₂)
                 >>= executeStackCheckSig msg₁




{-
and check that this is correct
-}

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
private
--abstract
  p2PKHNonEmptyStackAbstr : (msg₁ : Msg)(pbk : ℕ)(stack₂ : Stack)(cmp : ℕ)
                                → Maybe Stack
  p2PKHNonEmptyStackAbstr msg₁ pbk stack₂ cmp
       =  executeStackVerify (cmp ∷  pbk ∷ stack₂) >>= executeStackCheckSig msg₁



{- and we show that this is the right function
-}

-- This function will be repeated in stackVerificationP2PKHextractedProgram.agda
-- and therefore is kept private in this section in order to avoid a conflict
private
  stackfunP2PKHNonEmptyStackAbstractedCor :  (pubKeyHash : ℕ)(time₁ : Time)(msg₁ : Msg)(pbk : ℕ)(stack₂ : Stack)
                  → ⟦ scriptP2PKHᵇ pubKeyHash ⟧ˢ time₁ msg₁ (pbk ∷ stack₂)
                     ≡ p2PKHNonEmptyStackAbstr  msg₁ pbk stack₂
                             (compareNaturals pubKeyHash (hashFun pbk))
  stackfunP2PKHNonEmptyStackAbstractedCor pubKeyHash time₁ msg₁ pbk stack₂ = refl


{- Now we investigate what  p2PKHNonEmptyStackAbstr
When looking at it and see that

 p2PKHNonEmptyStackAbstr msg₁ pbk stack₂ cmp

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
testStackfunP2PKHNonEmptyStackAbstractedCompre0 = p2PKHNonEmptyStackAbstr msg₁ pbk stack₁ 0

{- if we evaluate it we get

nothing


We  show now this is always the case

-}

-- This function will be repeated in stackVerificationP2PKHextractedProgram.agda
-- and therefore is kept private in this section in order to avoid a conflict
private
  stackfunP2PKHNonEmptyStackAbstractedCorCompr0IsNothing : (msg₁ : Msg)(pbk : ℕ)(stack₂ : Stack)
        →  p2PKHNonEmptyStackAbstr msg₁ pbk stack₂ 0 ≡ nothing
  stackfunP2PKHNonEmptyStackAbstractedCorCompr0IsNothing msg₁ pbk stack₂ = refl


{- Now we look at what happens  if the value is non zero -}


testStackfunP2PKHNonEmptyStackAbstractedCompreSucCase : Maybe Stack
testStackfunP2PKHNonEmptyStackAbstractedCompreSucCase = p2PKHNonEmptyStackAbstr msg₁ pbk stack₁ (suc x₁)

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

p2PKHNonEmptyStackAbstr msg₁ pbk stack₁ x

stack₁ is [] or nonempty

So lets look at the easy case []

    -}


--easy case
testStackfunP2PKHNonEmptyStackAbstractedCompreSucEmpty : Maybe Stack
testStackfunP2PKHNonEmptyStackAbstractedCompreSucEmpty =
                           p2PKHNonEmptyStackAbstr msg₁ pbk [] (suc x₁)


{- if we evaluate it we get  result

nothing

we check that this always holds
-}


stackfunP2PKHNonEmptyStackAbstractedCorComprSucStackEmpty : (msg₁ : Msg)(pbk : ℕ)(x : ℕ)
             → p2PKHNonEmptyStackAbstr msg₁ pbk [] (suc x) ≡ nothing
stackfunP2PKHNonEmptyStackAbstractedCorComprSucStackEmpty msg₁ pbk x  = refl

{-  Intermezzo: we can see that the fanction gives always nothing if the stack is empty
   independent of the result

But this result is not really needed (so can be probably be ommitted in the paper)
   -}

-- This function will be repeated in stackVerificationP2PKHextractedProgram.agda
-- and therefore is kept private in this section in order to avoid a conflict
private
  stackfunP2PKHNonEmptyStackAbstractedCorEmptysNothing : (msg₁ : Msg)(pbk : ℕ)(x : ℕ)
        →  p2PKHNonEmptyStackAbstr msg₁ pbk [] x ≡ nothing

  stackfunP2PKHNonEmptyStackAbstractedCorEmptysNothing msg₁ pbk₁ zero = refl
  stackfunP2PKHNonEmptyStackAbstractedCorEmptysNothing msg₁ pbk₁ (suc x) = refl

{- Now we look at what happens if we have non empty stack₁ and comparision > 0
-}

{- if we evaluate it we get

just (boolToNat (isSigned  msg₁ sig₁ pbk) ∷ stack₁)



and we show that this is the case

-}

--stack nonempty
testStackfunP2PKHNonEmptyStackAbstractedCompreSucNonEmpty : Maybe Stack
testStackfunP2PKHNonEmptyStackAbstractedCompreSucNonEmpty = p2PKHNonEmptyStackAbstr msg₁ pbk (sig₁  ∷ stack₁) (suc x₁)



stackfunP2PKHNonEmptyStackAbstractedCorComprSucStackNonEmptyCor :
       (msg₁ : Msg)(pbk : ℕ)(x : ℕ)(sig₁ : ℕ)(stack₂ : Stack)
       → p2PKHNonEmptyStackAbstr msg₁ pbk (sig₁  ∷ stack₂) (suc x)
          ≡  just (boolToNat (isSigned  msg₁ sig₁ pbk) ∷ stack₂)
stackfunP2PKHNonEmptyStackAbstractedCorComprSucStackNonEmptyCor msg₂ pbk₁ sig₁ x stack₃ = refl

{- the following can be ommitted probably
   since we have digged out the function completely
   but here is anyway a theorem that the original function gives you nothing
         if the stack has hight 1 only

-}


{- this function is obolete but an interesting observation -}

stackfunP2PKHemptySingleStackIsNothing : (pubKeyHash : ℕ)(time₁ : Time)(msg₁ : Msg)(pbk : ℕ)
        → ⟦ scriptP2PKHᵇ pubKeyHash ⟧ˢ time₁ msg₁ (pbk ∷ []) ≡ nothing
stackfunP2PKHemptySingleStackIsNothing  pubKeyHash time₁ msg₁ pbk
  =  ⟦ scriptP2PKHᵇ pubKeyHash ⟧ˢ time₁ msg₁ (pbk ∷ [])
               ≡⟨ stackfunP2PKHNonEmptyStackAbstractedCor pubKeyHash time₁ msg₁ pbk []   ⟩
     p2PKHNonEmptyStackAbstr  msg₁ pbk [] (compareNaturals pubKeyHash (hashFun pbk))
               ≡⟨ stackfunP2PKHNonEmptyStackAbstractedCorEmptysNothing msg₁ pbk (compareNaturals pubKeyHash (hashFun pbk))   ⟩
     nothing
     ∎
