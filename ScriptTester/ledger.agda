open import basicBitcoinDataType

module ledger (param : GlobalParameters) where

open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Bool.Base hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
open import Data.List.NonEmpty hiding (head)
open import Data.Maybe

open import libraries.listLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.andLib
open import libraries.maybeLib

open import stack
open import instruction

record SignedWithSigPbk (msg : Msg)(address : Address) : Set where
  field  publicKey  :  PublicKey
         pbkCorrect :  param .publicKey2Address publicKey ≡ℕ  address
         signature  :  Signature
         signed     :  Signed param msg signature publicKey


-- record for the transaction field
record TXFieldNew : Set where
  constructor txFieldNew
  field  amount         :  ℕ
         address        :  Address
         smartContract  : BitcoinScript

open TXFieldNew public




txField2MsgNew : (inp : TXFieldNew) → Msg
txField2MsgNew inp  =   nat (amount inp) +msg nat (address inp)



txFieldList2MsgNew : (inp : List TXFieldNew) → Msg
txFieldList2MsgNew inp  = list (mapL txField2MsgNew inp)


txFieldList2TotalAmountNew : (inp : List TXFieldNew) → Amount
txFieldList2TotalAmountNew inp = sumListViaf amount inp



-- record for unsigned transaction
record TXUnsignedNew : Set where
  field  inputs   : List TXFieldNew
         outputs  : List TXFieldNew
         TXID1     : ℕ
open TXUnsignedNew public




txUnsigned2MsgNew :  (transac : TXUnsignedNew) → Msg
txUnsigned2MsgNew transac = txFieldList2MsgNew (inputs transac)  +msg txFieldList2MsgNew (outputs transac)




txInput2MsgNew : (inp : TXFieldNew)(outp : List TXFieldNew) → Msg
txInput2MsgNew inp outp = txField2MsgNew inp +msg txFieldList2MsgNew outp

tx2SignauxNew : (inp : List TXFieldNew) (outp : List TXFieldNew)  → Set
tx2SignauxNew []               outp  = ⊤
tx2SignauxNew (inp ∷ restinp)  outp  =
    SignedWithSigPbk (txInput2MsgNew inp outp) (address inp) ×  tx2SignauxNew restinp outp




tx2SignNew : TXUnsignedNew → Set
tx2SignNew tr = tx2SignauxNew (inputs tr) (outputs tr)

-- \bitcoinVersFive


record TXNew : Set where
  field  tx       : TXUnsignedNew
         cor      : txFieldList2TotalAmountNew (inputs tx) ≥ txFieldList2TotalAmountNew (outputs tx)
         nonEmpt  : NonNil (inputs tx) × NonNil (outputs tx)
         sig      : tx2SignNew tx

open TXNew public


--record for a ledger
record ledgerEntryNew : Set where   
  constructor ledgerEntrNew
  field ins       : BitcoinScript
        amount    : ℕ

open ledgerEntryNew public

record LedgerNew : Set where
  constructor ledger
  field
     entries        : (addr : Address) → Maybe ledgerEntryNew
     currentTime    : Time
open LedgerNew public


--record for transaction entry
record TXEntryNew : Set where
  constructor txentryNew
  field amount              : ℕ
        smartContract       : BitcoinScript
        address             : Address -- indentifiers for unspentTX outputs (UTXO) (Lists of UTXO)

open TXEntryNew public


testLedgerNewEntries : Address → Maybe ledgerEntryNew
testLedgerNewEntries zero = just (ledgerEntrNew [] 50)
testLedgerNewEntries (suc zero) = just (ledgerEntrNew [] 80)
testLedgerNewEntries (suc (suc x)) = nothing

testLedgerNew : LedgerNew
testLedgerNew .entries = testLedgerNewEntries
testLedgerNew .currentTime = 31

-- record for transaction
record transactionNew : Set where 
  constructor transactNew
  field txid      : ℕ
        inputs    : TXEntryNew
        outputs   : TXEntryNew

open transactionNew public

-- function that is used to check if the coins go to the same address
processLedger : LedgerNew →  transactionNew  → LedgerNew
processLedger oldLed
              (transactNew txid₁ (txentryNew amount₁ smartContract₁ recipientAddress)
                (txentryNew amount₂ smartContract₂ desinntationAddress))
              .entries addr
            =  if (addr ==b recipientAddress)
               then nothing
               else ( if (addr ==b desinntationAddress)
                      then  just (ledgerEntrNew smartContract₂  amount₂)
                      else  oldLed .entries addr )
processLedger oldLed trans .currentTime = suc (oldLed .currentTime)

tx2MsgNew : transactionNew → Msg
tx2MsgNew  t  = nat (txid t)
