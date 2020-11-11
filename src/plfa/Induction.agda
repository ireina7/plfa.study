module plfa.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)


{- This chapter we try to prove some more interesting things:) -}
_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎


+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m') n p =
  begin
    (suc m' + n) + p
  ≡⟨⟩
    suc (m' + n) + p
  ≡⟨⟩
    suc ((m' + n) + p)
  ≡⟨ cong suc (+-assoc m' n p) ⟩
    suc (m' + (n + p))
  ≡⟨⟩
    suc m' + (n + p)
  ∎


+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎

+-identityʳ (suc m') =
  begin
    (suc m') + zero
  ≡⟨⟩
    suc (m' + zero)
  ≡⟨ cong suc (+-identityʳ m') ⟩
    suc m'
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎


+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl


{- Exercise +-swap -}
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap zero n p = refl
+-swap (suc m) n p =
  begin
    suc (m + (n + p))
  ≡⟨ cong suc (+-swap m n p) ⟩
    suc (n + (m + p))
  ≡⟨ sym (+-suc n (m + p)) ⟩
    n + suc (m + p)
  ∎


*-identity : ∀ (m : ℕ) → m * 0 ≡ 0
*-identity zero = refl
*-identity (suc n) =
  begin
    suc n * 0
  ≡⟨⟩
    (n * 0)
  ≡⟨ *-identity n ⟩
    0
  ∎

*-suc : ∀ (m n : ℕ) → m * (suc n) ≡ m + (m * n)
*-suc 0 n = refl
*-suc (suc m') n =
  begin
    (suc m') * (suc n)
  ≡⟨⟩
    (suc n) + (m' * suc n)
  ≡⟨ cong (suc n +_) (*-suc m' n) ⟩
    suc n + (m' + (m' * n))
  ≡⟨ cong suc (sym (+-assoc n m' (m' * n))) ⟩
    suc (n + m' + m' * n)
  {- This makes me miss hole syntax suagr of scala -}
  ≡⟨ cong (\mn -> suc (mn + m' * n)) (+-comm n m') ⟩
    suc (m' + n + m' * n)
  ≡⟨ cong suc (+-assoc m' n (m' * n)) ⟩
    suc (m' + (n + m' * n))
  ∎

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero =
  begin
    m * zero
  ≡⟨ *-identity m ⟩
    0
  ≡⟨⟩
    0 * m
  ∎
*-comm m (suc n') =
  begin
    m * (suc n')
  ≡⟨ *-suc m n' ⟩
    m + m * n'
  ≡⟨ cong (m +_) (*-comm m n') ⟩
    m + n' * m
  ∎


*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ m n 0 =
  begin
    (m + n) * 0
  ≡⟨ *-comm (m + n) 0 ⟩
    0
  ≡⟨⟩
    0 * m + 0 * n
  ≡⟨ cong (_+ 0 * n) (*-comm 0 m) ⟩
    m * 0 + 0 * n
  ≡⟨ cong (m * 0 +_) (*-comm 0 n) ⟩
    m * 0 + n * 0
  ∎
{-
  Well, yes I know this is ugly and silly,
  but I didn't understand rewrite that time, so :)
-}
*-distrib-+ m n (suc p) =
  begin
    (m + n) * (suc p)
  ≡⟨ *-comm (m + n) (suc p) ⟩
    suc p * (m + n)
  ≡⟨⟩
    (m + n) + (p * (m + n))
  ≡⟨ cong ((m + n) +_) (*-comm p (m + n)) ⟩
    m + n + (m + n) * p
  ≡⟨ cong ((m + n) +_) (*-distrib-+ m n p) ⟩
    m + n + (m * p + n * p)
  ≡⟨ cong (_+ (m * p + n * p)) (+-comm m n) ⟩
    n + m + (m * p + n * p)
  ≡⟨ +-assoc n m (m * p + n * p) ⟩
    n + (m + (m * p + n * p))
  ≡⟨ cong (n +_) (sym (+-assoc m (m * p) (n * p))) ⟩
    n + (m + m * p + n * p)
  ≡⟨ cong (\mn -> n + (mn + n * p)) (sym (*-suc m p)) ⟩
    n + (m * suc p + n * p)
  ≡⟨ cong (n +_) (+-comm (m * suc p) (n * p)) ⟩
    n + (n * p + m * suc p)
  ≡⟨ sym (+-assoc n (n * p) (m * suc p)) ⟩
    n + n * p + m * suc p
  ≡⟨ cong (_+ m * suc p) (sym (*-suc n p)) ⟩
    n * suc p + m * suc p
  ≡⟨ +-comm (n * suc p) (m * suc p) ⟩
    m * suc p + n * suc p
  ∎


*-distrib-+′ : (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+′ zero n p = refl
*-distrib-+′ (suc m) n p
  rewrite *-distrib-+′ m n p
  | sym (+-assoc p (m * p) (n * p)) = refl


*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p
  rewrite *-distrib-+ n (m * n) p
  | *-assoc m n p = refl


0∸n≡0 : ∀ (n : ℕ) → 0 ∸ n ≡ 0
0∸n≡0 0 = refl
0∸n≡0 (suc n') = refl

∸-|-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-|-assoc zero n p
  rewrite 0∸n≡0 n | 0∸n≡0 p | 0∸n≡0 (n + p) = refl
∸-|-assoc (suc m) zero p = refl
∸-|-assoc (suc m) (suc n) p
  rewrite ∸-|-assoc m n p = refl


^-distribˡ-|-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-|-* m zero p rewrite +-identityʳ (m ^ p) = refl
^-distribˡ-|-* m (suc n) p
  rewrite ^-distribˡ-|-* m n p
  | *-assoc m (m ^ n) (m ^ p) = refl
