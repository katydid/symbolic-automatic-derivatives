-- A complete translation to Lean from Agda of
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/SizedAutomatic.lagda

-- SizedAutomatic.lean is a variation on Automatic.lean, in that it adds a size parameter to the definition of Lang.

-- The idea is that Automatic.lean and Symoblic.lean are duals of each other.
-- The definitions of null and derive for each operator, should look as similar to each other as possible.
-- Reusing the same definitions in Language.lean and proofs in Calculus.lean.

-- Automatic.lean is defined row based, it has a complete definition for each single operator
-- as opposed to Symbolic.lean which is defined row based and requires all operators to define a single function.
-- Automatic.lean gives the flexibility to the user of the library to add their own operators.
-- It is almost like each operator is a type class, that needs to implement the derive and null functions.

import Sadol.Decidability
import Sadol.Function
import Sadol.Language
import Sadol.Calculus

namespace SizedAutomatic

-- record Lang (P : ◇.Lang) : Set (suc ℓ) where
--   coinductive
--   field
--     ν : Dec (◇.ν P)
--     δ : (a : A) → Lang (◇.δ P a)

-- {-# BUILTIN SIZE     Size     #-}
-- {-# BUILTIN SIZELT   Size<_   #-}
-- i : Size
-- record Lang i (P : ◇.Lang) : Set (suc ℓ) where
--   coinductive
--   field
--     ν : Dec (◇.ν P)
--     δ : ∀ {j : Size< i} → (a : A) → Lang j (◇.δ P a)

inductive Lang {i: Nat} {α: Type u} : Language.Lang α -> Type (u+1) where
  | mk
    (null: Decidability.Dec (Calculus.null R))
    (derive: {j: Nat} -> (a: α) -> @Lang j α (Calculus.derive R a))
    : Lang R

def null (l: Lang R): Decidability.Dec (Calculus.null R) :=
  match l with
  | Lang.mk n _ => n

def derive {α: Type u} {R: Language.Lang α} (l: Lang R) (a: α): Lang (Calculus.derive R a) :=
  match l with
  | Lang.mk _ d => d a

-- ∅    : Lang i ◇.∅
def emptyset {α: Type u}: Lang (@Language.emptyset.{u} α) := Lang.mk
  -- ν ∅ = ⊥‽
  (null := Decidability.empty)
  -- δ ∅ a = ∅
  (derive := fun (a: α) => emptyset)

-- 𝒰    : Lang i ◇.𝒰
def universal {α: Type u}: Lang (@Language.universal.{u} α) := Lang.mk
  -- ν 𝒰 = ⊤‽
  (null := Decidability.unit)
  -- δ 𝒰 a = 𝒰
  (derive := fun _ => universal)


-- _∪_  : Lang i  P  → Lang i Q  → Lang i (P  ◇.∪  Q)
def or {α: Type u} {P Q: Language.Lang α} (p: Lang P) (q: Lang Q): Lang (Language.or P Q) := Lang.mk
  -- ν (p ∪ q) = ν p ⊎‽ ν q
  (null := Decidability.sum (null p) (null q))
  -- δ (p ∪ q) a = δ p a ∪ δ q a
  (derive := fun (a: α) => or (derive p a) (derive q a))

-- _∩_  : Lang i  P  → Lang i Q  → Lang i (P  ◇.∩  Q)
def and {α: Type u} {P Q: Language.Lang α} (p: Lang P) (q: Lang Q): Lang (Language.and P Q) := Lang.mk
  -- ν (p ∩ q) = ν p ×‽ ν q
  (null := Decidability.prod (null p) (null q))
  -- δ (p ∩ q) a = δ p a ∩ δ q a
  (derive := fun (a: α) => and (derive p a) (derive q a))

-- _·_  : Dec     s  → Lang i P  → Lang i (s  ◇.·  P)
def scalar {α: Type u} {P: Language.Lang α} (s: Decidability.Dec S) (p: Lang P): Lang (Language.scalar S P) := Lang.mk
  -- ν (s · p) = s ×‽ ν p
  (null := Decidability.prod s (null p))
  -- δ (s · p) a = s · δ p a
  (derive := fun (a: α) => scalar s (derive p a))

-- _◂_  : (Q ⟷ P) → Lang i P → Lang i Q
def iso {α: Type u} {P Q: Language.Lang α} (f: ∀ {w: List α}, Q w <=> P w) (p: Lang P): Lang Q := Lang.mk
  -- ν (f ◂ p) = f ◃ ν p
  (null := Decidability.apply' f (null p))
  -- δ (f ◂ p) a = f ◂ δ p a
  (derive := fun (a: α) => iso f (derive p a))

-- 𝟏    : Lang i ◇.𝟏
def emptystr {α: Type u}: Lang (@Language.emptystr α) := Lang.mk
  -- ν 𝟏 = ν𝟏 ◃ ⊤‽
  (null := Decidability.apply' Calculus.null_emptystr Decidability.unit)
  -- δ 𝟏 a = δ𝟏 ◂ ∅
  (derive := fun _ => iso Calculus.derive_emptystr emptyset)

-- _⋆_  : Lang i  P  → Lang i Q  → Lang i (P  ◇.⋆  Q)
def concat {α: Type u} {P Q: Language.Lang α} (p: Lang P) (q: Lang Q): Lang (Language.concat P Q) := Lang.mk
  -- ν (p ⋆ q) = ν⋆ ◃ (ν p ×‽ ν q)
  (null := Decidability.apply' Calculus.null_concat (Decidability.prod (null p) (null q)))
  -- δ (p ⋆ q) a = δ⋆ ◂ (ν p · δ q a ∪ δ p a ⋆ q)
  (derive := fun (a: α) =>
    (iso Calculus.derive_concat
      (scalar (null p)
        (or
          (derive q a)
          (concat (derive p a) q)
        )
      )
    )
  )

-- _☆   : Lang i  P  → Lang i (P ◇.☆)
def star {α: Type u} {P: Language.Lang α} (p: Lang P): Lang (Language.star P) := Lang.mk
  -- ν (p ☆) = ν☆ ◃ (ν p ✶‽)
  (null := Decidability.apply' Calculus.null_star (Decidability.list (null p)))
  -- δ (p ☆) a = δ☆ ◂ (ν p ✶‽ · (δ p a ⋆ p ☆))
  (derive := fun (a: α) =>
    (iso Calculus.derive_star
      (scalar
        (Decidability.list (null p))
        (concat (derive p a) (star p))
      )
    )
  )

-- `    : (a : A) → Lang i (◇.` a)
def char {α: Type u} [Decidability.DecEq α] (c: α): Lang (Language.char c) := Lang.mk
  -- ν (` a) = ν` ◃ ⊥‽
  (null := Decidability.apply' Calculus.null_char Decidability.empty)
  -- δ (` c) a = δ` ◂ ((a ≟ c) · 𝟏)
  (derive := fun (a: α) =>
    let cmp: Decidability.Dec (a ≡ c) := Decidability.decEq a c
    (iso Calculus.derive_char
      (scalar cmp emptystr)
    )
  )

-- ⟦_⟧‽ : Lang ∞ P → Decidable P
-- ⟦ p ⟧‽     []    = ν p
-- ⟦ p ⟧‽ (a  ∷ w)  = ⟦ δ p a ⟧‽ w
def decDenote (p: Lang P): Decidability.DecPred P :=
  fun w =>
    match w with
    | [] => null p
    | (a :: w) => decDenote (derive p a) w

-- ⟦_⟧ : Lang ∞ P → ◇.Lang
-- ⟦_⟧ {P} _ = P
def denote (_: @Lang α P): Language.Lang α := P

end SizedAutomatic
