-- A complete translation to Lean from Agda of
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/Decidability.lagda
-- except for the explicit TODOs found in this file.

import Sadol.Function

namespace Decidability

-- Agda:
--   data Dec (A: Set l):Set l where
--     yes: A → Dec A
--     no :¬A → Dec A
-- Lean Prop:
--   class inductive Decidable (p : Prop) where
--     | isFalse (h : Not p) : Decidable p
--     | isTrue (h : p) : Decidable p
class inductive Dec (P: Type u): Type u where
  | yes: P -> Dec P
  | no: (P -> PEmpty.{u + 1}) -> Dec P

-- Agda:
--   Decidable : (X → Set ℓ) → Set ℓ
--   Decidable P = ∀ x → Dec (P x)
-- Lean Prop:
--   abbrev DecidablePred {α : Sort u} (r : α → Prop) :=
--     (a : α) → Decidable (r a)
abbrev DecPred {α : Type u} (P : α → Type u) :=
  (a : α) → Dec (P a)

-- Agda
--   Decidable₂ : (A → B → Set ℓ) → Set ℓ
--   Decidable₂ _∼_ = ∀ a b → Dec (a ∼ b)
-- Lean Prop:
--   abbrev DecidableRel {α : Sort u} (r : α → α → Prop) :=
--     (a b : α) → Decidable (r a b)
abbrev DecRel {α : Type u} (r : α → α → Type u) :=
  (a b : α) → Dec (r a b)

-- ¬⇃_ : Set ℓ → Set ℓ
-- ¬⇃ X = X → ⊥
def not (α: Type u): Type u :=
  α -> PEmpty.{u + 1}

abbrev DecEq (α : Type u) :=
  (a b : α) → Dec (a ≡ b)

-- module Symbolic {ℓ} {A : Set ℓ} (_≟_ : Decidable₂ {A = A} _≡_) where
def decEq {α : Type u} [inst : DecEq α] (a b : α) : Dec (a ≡ b) :=
  inst a b

-- ⊥? : Dec ⊥
-- ⊥? = no(𝜆())
def empty : Dec PEmpty :=
  Dec.no (by intro; contradiction)

-- ⊤‽  : Dec ⊤
-- ⊤‽  = yes tt
def unit : Dec PUnit :=
  Dec.yes PUnit.unit

-- _⊎‽_  : Dec A → Dec B → Dec (A ⊎ B)
-- no ¬a  ⊎‽ no ¬b  = no [ ¬a , ¬b ]
-- yes a  ⊎‽ no ¬b  = yes (inj₁ a)
-- _      ⊎‽ yes b  = yes (inj₂ b)
def sum {α β: Type u} (a: Dec α) (b: Dec β): Dec (α ⊕ β) :=
  match (a, b) with
  | (Dec.no a, Dec.no b) =>
    Dec.no (fun ab =>
      match ab with
      | Sum.inl sa => a sa
      | Sum.inr sb => b sb
    )
  | (Dec.yes a, Dec.no _) =>
    Dec.yes (Sum.inl a)
  | (_, Dec.yes b) =>
    Dec.yes (Sum.inr b)

-- _×‽_  : Dec A → Dec B → Dec (A × B)
-- yes a  ×‽ yes b  = yes (a , b)
-- no ¬a  ×‽ yes b  = no (¬a ∘ proj₁)
-- _      ×‽ no ¬b  = no (¬b ∘ proj₂)
def prod {α β: Type u} (a: Dec α) (b: Dec β): Dec (α × β) :=
  match (a, b) with
  | (Dec.yes a, Dec.yes b) => Dec.yes (Prod.mk a b)
  | (Dec.no a, Dec.yes _) => Dec.no (fun ⟨a', _⟩ => a a')
  | (_, Dec.no b) => Dec.no (fun ⟨_, b'⟩ => b b')

-- _✶‽ : Dec A → Dec (A ✶)
-- _ ✶‽ = yes []
def list {α: Type u}: Dec α -> Dec (List α) :=
  fun _ => Dec.yes []

-- map′ : (A → B) → (B → A) → Dec A → Dec B
-- map′ A→B B→A (yes a) = yes (A→B a)
-- map′ A→B B→A (no ¬a) = no (¬a ∘ B→A)
def map' {α β: Type u} (ab: α -> β) (ba: β -> α) (deca: Dec α): Dec β :=
  match deca with
  | Dec.yes a =>
    Dec.yes (ab a)
  | Dec.no nota =>
    Dec.no (nota ∘ ba)

-- map‽⇔ : A ⇔ B → Dec A → Dec B
-- map‽⇔ A⇔B = map′ (to ⟨$⟩_) (from ⟨$⟩_) where open Equivalence A⇔B
def map {α β: Type u} (ab: α <=> β) (deca: Dec α): Dec β :=
  map' ab.toFun ab.invFun deca

-- _▹_ : A ↔ B → Dec A → Dec B
-- f ▹ a? = map‽⇔ (↔→⇔ f) a?
def apply {α β: Type u} (f: α <=> β) (deca: Dec α): Dec β :=
  map f deca

-- TODO: rewrite Agda into Lean
-- _▸_ : (P ⟷ Q) → Decidable P → Decidable Q
-- (f ▸ p?) w = f ▹ p? w

-- _◃_ : B ↔ A → Dec A → Dec B
-- g ◃ a? = ↔Eq.sym g ▹ a?
def apply' {α β: Type u} (f: β <=> α) (deca: Dec α): Dec β :=
  map f.sym deca

-- TODO: rewrite Agda into Lean
-- _◂_ : Q ⟷ P → Decidable P → Decidable Q
-- (g ◂ p?) w = g ◃ p? w

end Decidability
