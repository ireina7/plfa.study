module plfa.Naturals where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ


{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)


_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)


_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl


{- Exercise +-example -}
_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    suc (suc (suc 4))
  ≡⟨⟩
    7
  ∎


_*_ : ℕ → ℕ → ℕ
zero    * n = zero
(suc m) * n = n + (m * n)

{- Exercise *-example -}
_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    12
  ∎


_^_ : ℕ → ℕ → ℕ
m ^ 0 = 1
m ^ (suc n) = m * (m ^ n)

_ : 3 ^ 4 ≡ 81
_ = refl


_∸_ : ℕ → ℕ → ℕ
m ∸ zero      = m
zero ∸ suc n  = zero
suc m ∸ suc n = m ∸ n

_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎


{- Exercise ∸-example₁ -}
_ : 5 ∸ 3 ≡ 2
_ = refl


{- Exercise ∸-example₂ -}
_ : 3 ∸ 5 ≡ 0
_ = refl


infixl 6  _+_  _∸_
infixl 7  _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (xs O) = xs I
inc (xs I) = (inc xs) O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

to   : ℕ → Bin
from : Bin → ℕ

to zero = ⟨⟩ O
to (suc n) = inc (to n)

from ⟨⟩ = 0
from (xs O) = 2 * from xs
from (xs I) = 2 * from xs + 1
