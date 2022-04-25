module libraries.andLib  where

record _∧_ ( A B : Set ) : Set where
   constructor conj
   field
    and1 : A
    and2 : B
open _∧_  public



