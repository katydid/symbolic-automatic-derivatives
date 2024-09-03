-- A complete translation to Lean from Agda of
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/Symbolic.lagda

-- The idea is that Symoblic.lean and Automatic.lean are duals of each other.
-- The definitions of null and derive for each operator, should look as similar to each other as possible.
-- Reusing the same definitions in Language.lean and proofs in Calculus.lean.

-- Symbolic.lean is defined column based. This means it has a complete definition for each single function (null and derive),
-- but we need to complete the definition for each operator to finalize a function, so we only have two definitions.
-- Whereas Automatic.lean is defined row based and needs to define both functions for each single operator to complete a definition, so we have a definition per operator.
-- Symbolic.lean has definitions of null and derive that we are familiar with, but it doesn't allow the user of the library the flexibility to add their own operators.

import Sadol.Decidability
import Sadol.Function
import Sadol.Language
import Sadol.Calculus

namespace Symbolic

def Lang.emptyset: Language.Lang.{u} α := Language.emptyset

inductive Symb' {α: Type u} where
  -- ∅ : Lang ◇.∅
  | emptyset : Symb'
  -- 𝒰 : Lang ◇.𝒰
  | universal : Symb'
  -- 𝟏 : Lang ◇.𝟏
  | emptystr : Symb'
  -- ` : (a : A) → Lang (◇.` a)
  | char: (a: α) -> Symb'
  -- _∪_ : Lang P → Lang Q → Lang (P ◇.∪ Q)
  | or : Symb' -> Symb' -> Symb'

-- data Lang : ◇.Lang → Set (suc ℓ) where
inductive Symb: {α: Type u} -> Language.Lang.{u} α -> Type (u + 1) where
  -- ∅ : Lang ◇.∅
  | emptyset : Symb Lang.emptyset
  -- 𝒰 : Lang ◇.𝒰
  | universal : Symb Language.universal
  -- 𝟏 : Lang ◇.𝟏
  | emptystr : Symb Language.emptystr
  -- ` : (a : A) → Lang (◇.` a)
  | char: (a: α) -> Symb (Language.char a)
  -- _∪_ : Lang P → Lang Q → Lang (P ◇.∪ Q)
  | or : Symb P -> Symb Q -> Symb (Language.or P Q)
  -- _∩_ : Lang P → Lang Q → Lang (P ◇.∩ Q)
  | and : Symb P -> Symb Q -> Symb (Language.and P Q)
  -- _·_ : Dec s → Lang P → Lang (s ◇.· P)
  | scalar {s: Type u}: (Decidability.Dec s) -> Symb P -> Symb (Language.scalar s P)
  -- _⋆_ : Lang  P → Lang Q → Lang (P ◇.⋆ Q)
  | concat : Symb P -> Symb Q -> Symb (Language.concat P Q)
  -- _☆  : Lang P → Lang (P ◇.☆)
  | star : Symb P -> Symb (Language.star P)
  -- _◂_  : (Q ⟷ P) → Lang P → Lang Q
  -- "The reason _◀_ must be part of the inductive representation is the same as the other constructors, namely so that the core lemmas (Figure 3) translate into an implementation in terms of that representation."
  -- This is also used in the definition derive as the result of various operators.
  | iso {P Q: Language.Lang α}: (∀ {w: List α}, Q w <=> P w) -> Symb P -> Symb Q

export Symb (emptyset universal emptystr char or and scalar concat star iso)

-- ν  : Lang P → Dec (◇.ν P)
def null (l: Symb R): Decidability.Dec (Calculus.null R) :=
  match l with
  -- ν ∅ = ⊥‽
  | emptyset => Decidability.empty
  -- ν 𝒰 = ⊤‽
  | universal => Decidability.unit
  -- ν 𝟏 = ν𝟏 ◃ ⊤‽
  | emptystr => Decidability.apply' Calculus.null_emptystr Decidability.unit
  -- ν (p ∪ q) = ν p ⊎‽ ν q
  | or p q => Decidability.sum (null p) (null q)
  -- ν (p ∩ q) = ν p ×‽ ν q
  | and p q => Decidability.prod (null p) (null q)
  -- ν (s · p) = s ×‽ ν p
  | scalar s p => Decidability.prod s (null p)
  -- ν (p ⋆ q) = ν⋆ ◃ (ν p ×‽ ν q)
  | concat p q => Decidability.apply' Calculus.null_concat (Decidability.prod (null p) (null q))
  -- ν (p ☆) = ν☆ ◃ (ν p ✶‽)
  | star p => Decidability.apply' Calculus.null_star (Decidability.list (null p))
  -- ν (` a) = ν` ◃ ⊥‽
  | char a => Decidability.apply' Calculus.null_char Decidability.empty
  -- ν (f ◂ p) = f ◃ ν p
  | iso f p => Decidability.apply' f (null p)

-- δ  : Lang P → (a : A) → Lang (◇.δ P a)
def Symb.derive [Decidability.DecEq α] (l: Symb P) (a: α): Symb (Calculus.derive P a) :=
  match l with
  -- δ ∅ a = ∅
  | emptyset => emptyset
  -- δ 𝒰 a = 𝒰
  | universal => universal
  -- δ (p ∪ q) a = δ p a ∪ δ q a
  | or p q => or (derive p a) (derive q a)
  -- δ (p ∩ q) a = δ p a ∩ δ q a
  | and p q => and (derive p a) (derive q a)
  -- δ (s · p) a = s · δ p a
  | scalar s p => scalar s (derive p a)
  -- δ 𝟏 a = δ𝟏 ◂ ∅
  | emptystr => (iso Calculus.derive_emptystr emptyset)
  -- δ (p ⋆ q) a = δ⋆ ◂ (ν p · δ q a ∪ δ p a ⋆ q)
  | concat p q =>
    (iso Calculus.derive_concat
      (scalar (null p)
        (or
          (derive q a)
          (concat (derive p a) q)
        )
      )
    )
  -- δ (p ☆) a = δ☆ ◂ (ν p ✶‽ · (δ p a ⋆ p ☆))
  | star p =>
    (iso Calculus.derive_star
      (scalar
        (Decidability.list (null p))
        (concat (derive p a) (star p))
      )
    )
  -- δ (` c) a = δ` ◂ ((a ≟ c) · 𝟏)
  | char c =>
    let cmp: Decidability.Dec (a ≡ c) := Decidability.decEq a c
    (iso Calculus.derive_char
      (scalar cmp emptystr)
    )
  -- δ (f ◂ p) a = f ◂ δ p a
  | iso f p => iso f (derive p a)

-- ⟦_⟧‽ : Lang P → Decidable P
-- ⟦ p ⟧‽     []    = ν p
-- ⟦ p ⟧‽ (a  ∷ w)  = ⟦ δ p a ⟧‽ w
def Symb.denote [Decidability.DecEq α] {P: Language.Lang α} (p: Symb P):
  ∀ (w: List α), Decidability.Dec (P w) :=
  fun w => match w with
  | [] => null p
  | (a :: as) => Symb.denote (Symb.derive p a) as

-- ⟦_⟧ : Lang P → ◇.Lang
-- ⟦_⟧ {P} r = P
def denote (_: @Symb α P): Language.Lang α := P

end Symbolic
