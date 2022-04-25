open import basicBitcoinDataType

module verificationStackScripts.stackVerificationP2PKHUsingEqualityOfProgramsTest (param : GlobalParameters) where


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





postulate timeTest : Time
postulate msgTest₁ : Msg
postulate stackTest : Stack
postulate stackTest2 : Stack
postulate pbkhTest : ℕ
postulate pbk : ℕ
postulate xTest : ℕ
postulate sigTest : ℕ
postulate yTest : ℕ


{- We first create a symbolic execution of the scriptP2PKH pbkhTest to see what kind
   of case distinction happens -}

check = scriptP2PKHᵇ


testP2PKHscript : Maybe Stack
testP2PKHscript = ⟦ scriptP2PKHᵇ pbkhTest ⟧ˢ timeTest msgTest₁ stackTest





{- evaluation of testP2PKHscript returns

executeStackDup stackTest >>=
(λ stack₁ →
   executeOpHash stack₁ >>=
   (λ stack₂ →
      executeStackEquality (pbkhTest ∷ stack₂) >>=
      (λ stack₄ →
         executeStackVerify stack₄ >>=
         (λ stack₄ → executeStackCheckSig msgTest₁ stack₄))))

-}


{-
If we execute the last line
(executeStackDup stackTest)

we see it will give
nothing if stackTest = []
just something if stackTest is nonempty

So let's check what happens if stackTest = []
-}



testP2PKHscriptEmpty : Maybe Stack
testP2PKHscriptEmpty = ⟦ scriptP2PKHᵇ pbkhTest ⟧ˢ timeTest msgTest₁ []




{- if we evaluate testP2PKHscriptEmpty we get:

nothing

So now get the first (trivial) theorem
(without the postulated parameters)
-}



stackfunP2PKHemptyIsNothing : (pubKeyHash : ℕ)(time₁ : Time)(msg₁ : Msg)
                              → ⟦ scriptP2PKHᵇ pubKeyHash ⟧ˢ time₁ msg₁ [] ≡ nothing
stackfunP2PKHemptyIsNothing pubKeyHash time₁ msg₁ = refl




{- Now we look at what happens if the stack is non empty -}



teststackfunP2PKHNonEmptyStack :  Maybe Stack
teststackfunP2PKHNonEmptyStack =  ⟦ scriptP2PKHᵇ pbkhTest ⟧ˢ timeTest msgTest₁ (pbk ∷ stackTest)


{- If we evaluate teststackfunP2PKHNonEmptyStack we get

executeStackVerify (compareNaturals pbkhTest (hashfun pbk) ∷ pbk ∷ stackTest)
>>= (λ stack₁ → executeStackCheckSig msgTest₁ stack₁)


We see that

(λ stack₁ → executeStackCheckSig msgTest₁ stack₁) = executeStackCheckSig msgTest₁

and can therefore use


executeStackVerify (compareNaturals pbkhTest (hashfun pbk) ∷ pbk ∷ stackTest)
>>= executeStackCheckSig msgTest₁


 -}



stackfunP2PKHNonEmptyStack : (pubKeyHash : ℕ)(msg₁ : Msg)(pbk : ℕ)(stack₁ : Stack) → Maybe Stack
stackfunP2PKHNonEmptyStack pubKeyHash msg₁ pbk stack₁
              = executeStackVerify (compareNaturals pubKeyHash (hashFun pbk) ∷ pbk ∷ stack₁)
                >>= executeStackCheckSig msg₁



-- and check that this is correct

stackfunP2PKHemptyNonEmptyStackCorrect : (pubKeyHash : ℕ)(time₁ : Time)(msg₁ : Msg)(pbk : ℕ)(stack₁ : Stack)
        → ⟦ scriptP2PKHᵇ pubKeyHash  ⟧ˢ time₁ msg₁ (pbk ∷ stack₁) ≡ stackfunP2PKHNonEmptyStack pubKeyHash msg₁  pbk stack₁
stackfunP2PKHemptyNonEmptyStackCorrect pubKeyHash time₁ msg₁ pbk stack₁ = refl



{- We see now the case distinction depends on
   compres := compareNaturals pbkhTest (hashFun pbk)

since

executeStackVerify    (compres ∷  pbk ∷ stackTest)

will depend on whether compres is 0 or  suc x'

so we abstract from

compres = compareNaturals pubKeyHash (hashFun pbk)

-}

stackfunP2PKHNonEmptyStackAbstracted : (msg₁ : Msg)(pbk : ℕ)(stack₁ : Stack)(compareRes : ℕ)
                               → Maybe Stack
stackfunP2PKHNonEmptyStackAbstracted msg₁ pbk stack₁ compareRes
       =  executeStackVerify (compareRes ∷  pbk ∷ stack₁) >>= executeStackCheckSig msg₁


-- and we show that this is the right function

stackfunP2PKHNonEmptyStackAbstractedCor :  (pubKeyHash : ℕ)(time₁ : Time)(msg₁ : Msg)(pbk : ℕ)(stack₁ : Stack)
                → ⟦ scriptP2PKHᵇ pubKeyHash ⟧ˢ time₁ msg₁ (pbk ∷ stack₁)
                   ≡ stackfunP2PKHNonEmptyStackAbstracted  msg₁ pbk stack₁
                           (compareNaturals pubKeyHash (hashFun pbk))
stackfunP2PKHNonEmptyStackAbstractedCor pubKeyHash time₁ msg₁ pbk stack₁ = refl


{- Now we investigate stackfunP2PKHNonEmptyStackAbstracted
When looking at it we see that

 stackfunP2PKHNonEmptyStackAbstracted msg₁ pbk stack₁ compareRes

will evaluate
executeStackVerify (compareRes ∷  pbk ∷ stack₁)
which will in turn make a case disctintion on whether compareRes is 0 or  not zero

(that corresponds to what the original function does because it makes this comparison
   compareNaturals pubKeyHash (hashFun pbk)
  which checks  whether the pbk provided  by the user hashes to the pubKeyHash of the locking script
    if it  is 0 it should fail, and if it is 1 it should succeed.

So lets make the test
-}

testStackfunP2PKHNonEmptyStackAbstractedCompre0 : Maybe Stack
testStackfunP2PKHNonEmptyStackAbstractedCompre0 = stackfunP2PKHNonEmptyStackAbstracted msgTest₁ pbk stackTest 0

{- if we evaluate testStackfunP2PKHNonEmptyStackAbstractedCompre0 we get

nothing


We  show now this is always the case

-}

stackfunP2PKHNonEmptyStackAbstractedCorCompr0IsNothing : (msg₁ : Msg)(pbk : ℕ)(stack₁ : Stack)
      →  stackfunP2PKHNonEmptyStackAbstracted msg₁ pbk stack₁ 0 ≡ nothing
stackfunP2PKHNonEmptyStackAbstractedCorCompr0IsNothing msg₁ pbk stack₁ = refl


-- Now we look at what happens  if the value is non zero


testStackfunP2PKHNonEmptyStackAbstractedCompreSucCase : Maybe Stack
testStackfunP2PKHNonEmptyStackAbstractedCompreSucCase = stackfunP2PKHNonEmptyStackAbstracted msgTest₁ pbk stackTest (suc xTest)

{- if we evalute
     testStackfunP2PKHNonEmptyStackAbstractedCompreSucCase
    we get

executeStackCheckSig msgTest₁ (pbk ∷ stackTest)


This corresponds to the situation where
the original stack was non empty, and the comparision of the pbk with the pbkhash
got a result > 0



If we look at
executeStackCheckSig

we see that it gives nothing when the stack has height < 2
and otherwise does something,

so we can  make a case distinction on whether in

stackfunP2PKHNonEmptyStackAbstracted msg₁ pbk stack x

stack is [] or nonempty

So lets look at the easy case []

    -}



testStackfunP2PKHNonEmptyStackAbstractedCompreSucEmpty : Maybe Stack
testStackfunP2PKHNonEmptyStackAbstractedCompreSucEmpty =
                           stackfunP2PKHNonEmptyStackAbstracted msgTest₁ pbk [] (suc xTest)


{- if we evaluate testStackfunP2PKHNonEmptyStackAbstractedCompreSucEmpty we get  result

nothing

we check that this always holds
-}


stackfunP2PKHNonEmptyStackAbstractedCorComprSucStackEmpty : (msg₁ : Msg)(pbk : ℕ)(x : ℕ)
             → stackfunP2PKHNonEmptyStackAbstracted msg₁ pbk [] (suc x) ≡ nothing
stackfunP2PKHNonEmptyStackAbstractedCorComprSucStackEmpty msg₁ pbk x  = refl

{-  Intermezzo: we can see that stackfunP2PKHNonEmptyStackAbstractedCorComprSucStackEmpty returns always nothing if the stack is empty
   independent of the result

But this result is not really needed  -}



stackfunP2PKHNonEmptyStackAbstractedCorEmptysNothing : (msg₁ : Msg)(pbk : ℕ)(x : ℕ)
      →  stackfunP2PKHNonEmptyStackAbstracted msg₁ pbk [] x ≡ nothing

stackfunP2PKHNonEmptyStackAbstractedCorEmptysNothing msg₁ pbk₁ zero = refl
stackfunP2PKHNonEmptyStackAbstractedCorEmptysNothing msg₁ pbk₁ (suc x) = refl

-- Now we look at what happens if we have non empty stack and comparision > 0


{- if we evaluate stackfunP2PKHNonEmptyStackAbstractedCorEmptysNothing we get

just (boolToNat (isSigned  msgTest₁ sigTest pbk) ∷ stackTest)



and we show that this is the case

-}


testStackfunP2PKHNonEmptyStackAbstractedCompreSucNonEmpty : Maybe Stack
testStackfunP2PKHNonEmptyStackAbstractedCompreSucNonEmpty = stackfunP2PKHNonEmptyStackAbstracted msgTest₁ pbk (sigTest  ∷ stackTest) (suc xTest)



stackfunP2PKHNonEmptyStackAbstractedCorComprSucStackNonEmptyCor :
       (msg₁ : Msg)(pbk : ℕ)(x : ℕ)(sig₁ : ℕ)(stack₁ : Stack)
       → stackfunP2PKHNonEmptyStackAbstracted msg₁ pbk (sig₁  ∷ stack₁) (suc x)
          ≡  just (boolToNat (isSigned  msg₁ sig₁ pbk) ∷ stack₁)
stackfunP2PKHNonEmptyStackAbstractedCorComprSucStackNonEmptyCor msg₂ pbk₁ sig₁ x stack₂ = refl




{- this theorem is not needed but an interesting observation -}

stackfunP2PKHemptySingleStackIsNothing : (pubKeyHash : ℕ)(time₁ : Time)(msg₁ : Msg)(pbk : ℕ)
        → ⟦ scriptP2PKHᵇ pubKeyHash ⟧ˢ time₁ msg₁ (pbk ∷ []) ≡ nothing
stackfunP2PKHemptySingleStackIsNothing  pubKeyHash time₁ msg₁ pbk
  =  ⟦ scriptP2PKHᵇ pubKeyHash ⟧ˢ time₁ msg₁ (pbk ∷ [])
               ≡⟨ stackfunP2PKHNonEmptyStackAbstractedCor pubKeyHash time₁ msg₁ pbk []   ⟩
     stackfunP2PKHNonEmptyStackAbstracted  msg₁ pbk [] (compareNaturals pubKeyHash (hashFun pbk))
               ≡⟨ stackfunP2PKHNonEmptyStackAbstractedCorEmptysNothing msg₁ pbk (compareNaturals pubKeyHash (hashFun pbk))   ⟩
     nothing
     ∎

{- Now we have decoded the function -}

-- should be equal to stackfunP2PKHNonEmptyStackAbstracted (ignorning time)
pspkhFunctionDecodedaux1 : (pbk : ℕ)(msg₁ : Msg)(stack₁ : Stack)(cpRes : ℕ) → Maybe Stack
pspkhFunctionDecodedaux1 pbk msg₁ [] cpRes = nothing
pspkhFunctionDecodedaux1 pbk msg₁ (sig₁ ∷ stack₁) zero = nothing
pspkhFunctionDecodedaux1 pbk msg₁ (sig₁ ∷ stack₁) (suc cpRes) = just (boolToNat (isSigned  msg₁ sig₁ pbk) ∷ stack₁)

-- should be equal to   ⟦ scriptP2PKHᵇ pubKeyHash ⟧ˢ time₁ msg₁ stack₁   (where time is irrelevant)
pspkhFunctionDecoded : (pbkh : ℕ)(msg₁ : Msg)(stack₁ : Stack) → Maybe Stack
pspkhFunctionDecoded pbkh msg₁ [] = nothing
pspkhFunctionDecoded pbkh msg₁ (pbk ∷ stack₁) = pspkhFunctionDecodedaux1 pbk msg₁ stack₁ (compareNaturals pbkh (hashFun pbk))

-- we show it is correct


pspkhFunctionDecodedaux1cor : (pbk : ℕ)(msg₁ : Msg)(stack₁ : Stack)(cpRes : ℕ)
                          → stackfunP2PKHNonEmptyStackAbstracted msg₁ pbk stack₁ cpRes
                             ≡ pspkhFunctionDecodedaux1 pbk msg₁ stack₁ cpRes
pspkhFunctionDecodedaux1cor pbk₁ msg₁ [] cpRes = stackfunP2PKHNonEmptyStackAbstractedCorEmptysNothing msg₁ pbk₁ cpRes
pspkhFunctionDecodedaux1cor pbk₁ msg₁ (x ∷ stack₁) zero = refl
pspkhFunctionDecodedaux1cor pbk₁ msg₁ (x ∷ stack₁) (suc cpRes) = refl


pspkhFunctionDecodedcor : (time₁ : ℕ) (pbkh : ℕ)(msg₁ : Msg)(stack₁ : Stack)
           → ⟦ scriptP2PKHᵇ pbkh ⟧ˢ time₁ msg₁ stack₁  ≡ pspkhFunctionDecoded pbkh  msg₁ stack₁
pspkhFunctionDecodedcor time₁ pbkh msg₁ [] = refl
pspkhFunctionDecodedcor time₁ pbkh msg₁ (pbk ∷ stack₁) =
       ⟦ scriptP2PKHᵇ pbkh ⟧ˢ time₁ msg₁ (pbk ∷ stack₁)
          ≡⟨ stackfunP2PKHNonEmptyStackAbstractedCor pbkh time₁ msg₁ pbk stack₁ ⟩
       stackfunP2PKHNonEmptyStackAbstracted  msg₁ pbk stack₁ (compareNaturals pbkh (hashFun pbk))
          ≡⟨ pspkhFunctionDecodedaux1cor pbk msg₁ stack₁ (compareNaturals pbkh (hashFun pbk)) ⟩
       pspkhFunctionDecodedaux1 pbk msg₁ stack₁    (compareNaturals pbkh (hashFun pbk))
       ∎

-- Now we just verify the hoare triple for the function we have found



lemmaPHKcoraux3 : (x₁ : ℕ)(time : Time) (msg₁ : Msg) (x₂ : ℕ)(s : Stack) (x : ℕ) →
                 liftPred2Maybe (λ s₁ → acceptStateˢ time msg₁ s₁)
                  (pspkhFunctionDecodedaux1 x₁ msg₁ (x₂ ∷ s) x)
                  → ¬ (x ≡ 0)
lemmaPHKcoraux3 x₁ time msg₁ x₂ s zero () x₄
lemmaPHKcoraux3 x₁ time msg₁ x₂ s (suc x) x₃ ()

lemmaCompareNat2 : ( x y : ℕ ) → ¬ (compareNaturals x y ≡ 0) → x ≡ y
lemmaCompareNat2 zero zero p = refl
lemmaCompareNat2 zero (suc y) p = efq (p refl)
lemmaCompareNat2 (suc x) zero p = efq (p refl)
lemmaCompareNat2 (suc x) (suc y) p = cong suc (lemmaCompareNat2 x y p)


lemmaPHKcoraux2 : (pbk : ℕ)(time : Time) (msg₁ : Msg) (sig : ℕ)(s : Stack) (cpRes : ℕ) →
                 liftPred2Maybe (λ s₁ → acceptStateˢ time msg₁ s₁)
                  (pspkhFunctionDecodedaux1 pbk msg₁ (sig ∷ s) cpRes)
                  → NotFalse (boolToNat (isSigned  msg₁ sig pbk))
lemmaPHKcoraux2 pbk time msg₁ sig s (suc cpRes) x = x
