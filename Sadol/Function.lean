-- An approximation of the Function module in the Agda standard library.

import Sadol.Tipe

-- A ↔ B = Inverse A B

-- record Inverse : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
--   field
--     to        : A → B
--     from      : B → A
--     to-cong   : Congruent _≈₁_ _≈₂_ to
--     from-cong : Congruent _≈₂_ _≈₁_ from
--     inverse   : Inverseᵇ _≈₁_ _≈₂_ to from

-- Congruent : (A → B) → Set _
-- Congruent f = ∀ {x y} → x ≈₁ y → f x ≈₂ f y

-- Inverseᵇ : (A → B) → (B → A) → Set _
-- Inverseᵇ f g = Inverseˡ f g × Inverseʳ f g

-- Inverseˡ : (A → B) → (B → A) → Set _
-- Inverseˡ f g = ∀ {x y} → y ≈₁ g x → f y ≈₂ x

-- Inverseʳ : (A → B) → (B → A) → Set _
-- Inverseʳ f g = ∀ {x y} → y ≈₂ f x → g y ≈₁ x

-- (_≈₁_ : Rel A ℓ₁) -- Equality over the domain
-- (_≈₂_ : Rel B ℓ₂) -- Equality over the codomain

-- Rel : Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
-- Rel A ℓ = REL A A ℓ

-- REL : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ suc ℓ)
-- REL A B ℓ = A → B → Set ℓ

-- mk↔′ : ∀ (f : A → B) (f⁻¹ : B → A) → Inverseˡ f f⁻¹ → Inverseʳ f f⁻¹ → A ↔ B

-- If we look closely at mk↔′ it matches the Mathlib.Logic.Equiv.Defs
-- structure Equiv (α : Sort*) (β : Sort _) where
--   protected toFun : α → β
--   protected invFun : β → α
--   protected left_inv : LeftInverse invFun toFun
--   protected right_inv : RightInverse invFun toFun

def leftInverse {α β: Type u} (g : β → α) (f : α → β) : Type u :=
  ∀ x, g (f x) ≡ x

def rightInverse {α β: Type u} (g : β → α) (f : α → β) : Type u :=
  leftInverse f g

structure TEquiv (α : Type u) (β : Type u) where
  toFun : α → β
  invFun : β → α
  leftInv : leftInverse invFun toFun
  rightInv : rightInverse invFun toFun

-- We consider the three definitions of equivalent (Equiv, TEquiv and Agda's Inverse) to be equivalent

infixr:25 " <=> " => TEquiv

-- ↔Eq.sym
def TEquiv.sym (e: A <=> B): B <=> A :=
  ⟨e.invFun, e.toFun, e.rightInv, e.leftInv⟩

-- Extensional (or “pointwise”) isomorphism relates predicates isomorphic on every argument: P ←→ Q = ∀ {w} → P w ↔ Q w
def ETEquiv (a b: List α -> Type u) := ∀ {w: List α}, (a w) <=> (b w)

infixr:25 " ⟷ " => ETEquiv

-- Note: We see that proofs that need ⟷ are typically proven using mk↔′
-- δ𝟏  : δ 𝟏 a ⟷ ∅
-- δ𝟏 = mk↔′ (λ ()) (λ ()) (λ ()) (λ ())

-- Lean struggles to synthesize w sometimes, for example
--   (δ' ε a) ⟷ ∅
-- results in the error: "don't know how to synthesize implicit argument 'w'"
-- Then we need to explicitly provide 'w', as such
--   ∀ (w: List α), (δ' ε a) w <=> ∅ w
