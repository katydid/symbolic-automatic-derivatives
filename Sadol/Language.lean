-- A complete translation to Lean from Agda of
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/Language.lagda
-- except for `module AltStar where` and everything below found in Language.lagda.

import Sadol.Tipe

-- module Language {ℓ} (A : Set ℓ) where
namespace Language

-- Lang : Set (suc ℓ)
-- Lang = A ✶ → Set ℓ
def Lang (α : Type u) : Type (u + 1) :=
  List α -> Type u

-- ∅ : Lang
-- ∅ w = ⊥
def emptyset : Lang α :=
  -- PEmpty is Empty, but allows specifying the universe
  -- PEmpty is a Sort, which works for both Prop and Type
  fun _ => PEmpty

-- 𝒰 : Lang
-- 𝒰 w = ⊤
def universal {α: Type u} : Lang α :=
  -- PUnit is Empty, but allows specifying the universe
  -- PUnit is a Sort, which works for both Prop and Type
  fun _ => PUnit

-- 𝟏 : Lang
-- 𝟏 w = w ≡ []
def emptystr {α: Type u} : Lang α :=
  fun w => w ≡ []

-- ` : A → Lang
-- ` c w = w ≡ [ c ]
def char {α: Type u} (a : α): Lang α :=
  fun w => w ≡ [a]

-- infixl 7 _·_
-- _·_ : Set ℓ → Op₁ Lang
-- (s · P) w = s × P w
def scalar {α: Type u} (s : Type u) (P : Lang α) : Lang α :=
  fun w => s × P w

-- infixr 6 _∪_
-- _∪_ : Op₂ Lang
-- (P ∪ Q) w = P w ⊎ Q w
def or {α: Type u} (P : Lang α) (Q : Lang α) : Lang α :=
  fun w => P w ⊕ Q w

-- infixr 6 _∩_
-- _∩_ : Op₂ Lang
-- (P ∩ Q) w = P w × Q w
def and {α: Type u} (P : Lang α) (Q : Lang α) : Lang α :=
  fun w => P w × Q w

-- infixl 7 _⋆_
-- _⋆_ : Op₂ Lang
-- (P ⋆ Q) w = ∃⇃ λ (u ,  v) → (w ≡ u ⊙ v) × P u × Q v
def concat {α: Type u} (P : Lang α) (Q : Lang α) : Lang α :=
  fun (w : List α) =>
    Σ' (x : List α) (y : List α), (_px: P x) ×' (_qy: Q y) ×' w = (x ++ y)

inductive All {α: Type u} (P : α -> Type u) : (List α -> Type u) where
  | nil : All P []
  | cons : ∀ {x xs} (_px : P x) (_pxs : All P xs), All P (x :: xs)

-- infixl 10 _☆
-- _☆ : Op₁ Lang
-- (P ☆) w = ∃ λ ws → (w ≡ concat ws) × All P ws
def star {α: Type u} (P : Lang α) : Lang α :=
  fun (w : List α) =>
    Σ' (ws : List (List α)), (_pws: All P ws) ×' w = (List.flatten ws)

-- attribute [simp] allows these definitions to be unfolded when using the simp tactic.
attribute [simp] universal emptyset emptystr char scalar or and concat star

example: Lang α := universal
example: Lang α := emptystr
example: Lang α := (or emptystr universal)
example: Lang α := (and emptystr universal)
example: Lang α := emptyset
example: Lang α := (star emptyset)
example: Lang Char := char 'a'
example: Lang Char := char 'b'
example: Lang Char := (or (char 'a') emptyset)
example: Lang Char := (and (char 'a') (char 'b'))
example: Lang Nat := (and (char 1) (char 2))
example: Lang Nat := (scalar PUnit (char 2))
example: Lang Nat := (concat (char 1) (char 2))

end Language
