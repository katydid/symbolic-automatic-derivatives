-- A complete translation to Lean from Agda of
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/Calculus.lagda
-- except for the explicit TODOs found in this file.
-- and except for `Experiment with alternative star` and everything below found in Calculus.lagda.
-- and except functions that do not seem to be used: `ν∘foldlδ`, `νpureᵀ`, `νmapᵀ`, `νmapᵀ₂`, `ν✪` and `δ✪`.
-- Note: `ν✪` and `δ✪` might be useful for the proofs of null_star and derive_star, not sure.

import Sadol.Tipe
import Sadol.Function
import Sadol.Language

namespace Calculus

open Language
open List
open Char
open String

-- ν⇃ : Lang → Set ℓ
-- ν⇃ P = P []
def null' (P: Lang α): Type u :=
  P []

-- δ⇃ : Lang → A → Lang
-- δ⇃ P a w = P (a ∷ w)
def derive' (P: Lang α) (a: α): Lang α :=
  fun (w: List α) => P (a :: w)

-- ν : (A ✶ → B) → B
-- ν f = f []
def null {α: Type u} {β: Type v} (f: List α -> β): β :=
  f []

-- 𝒟 : (A ✶ → B) → A ✶ → (A ✶ → B)
-- 𝒟 f u = λ v → f (u ⊙ v)
def derives {α: Type u} {β: Type v} (f: List α -> β) (u: List α): (List α -> β) :=
  λ v => f (u ++ v)

-- δ : (A ✶ → B) → A → (A ✶ → B)
-- δ f a = 𝒟 f [ a ]
def derive {α: Type u} {β: Type v} (f: List α -> β) (a: α): (List α -> β) :=
  derives f [a]

attribute [simp] null derive derives

-- 𝒟[] : 𝒟 f [] ≡ f
-- 𝒟[] = refl
def derives_emptylist : derives f [] ≡ f :=
  trfl

-- _⊙_ : ∀ {A} → A ✶ → A ✶ → A ✶
-- _⊙_ = _++_
-- 𝒟⊙ : 𝒟 f (u ⊙ v) ≡ 𝒟 (𝒟 f u) v
-- 𝒟⊙ {u = []} = refl
-- 𝒟⊙ {f = f} {u = a ∷ u} = 𝒟⊙ {f = δ f a} {u = u}
def derives_strings (f: List α -> β) (u v: List α): derives f (u ++ v) ≡ derives (derives f u) v :=
  match u with
  | [] => trfl
  | (a :: u') => derives_strings (derive f a) u' v

-- ν∘𝒟 : ν ∘ 𝒟 f ≗ f
-- ν∘𝒟 u rewrite (++-identityʳ u) = refl
-- The paper says: "For functions f and g, f ≗ g is extensional equality, i.e., ∀ x → f x ≡ g x."
def null_derives (f: List α -> β) (u: List α): (null ∘ derives f) u ≡ f u := by
  simp
  exact trfl

-- 𝒟foldl : 𝒟 f ≗ foldl δ f
-- 𝒟foldl []        = refl
-- 𝒟foldl (a ∷ as)  = 𝒟foldl as
def derives_foldl (f: List α -> β) (u: List α): (derives f) u ≡ (List.foldl derive f) u :=
  match u with
  | [] => trfl
  | (a :: as) => by sorry
  -- TODO when trying to translate the Agda to Lean using:
  -- | (a :: as) => derives_foldl f as
  -- We get the following type error:
  -- type mismatch
  --   derives_foldl f as
  -- has type
  --   derives f as ≡ List.foldl derive f as : Type (max ?u.1250 ?u.1259)
  -- but is expected to have type
  --   derives f (a :: as) ≡ List.foldl derive f (a :: as) : Type (max ?u.1250 ?u.1259)

-- ν∅  : ν ∅ ≡ ⊥
-- ν∅ = refl
def null_emptyset {α: Type u}:
  @null α _ emptyset ≡ PEmpty :=
  trfl

-- ν𝒰  : ν 𝒰 ≡ ⊤
-- ν𝒰 = refl
def null_universal {α: Type u}:
  @null α _ universal ≡ PUnit :=
  trfl

-- ν𝟏  : ν 𝟏 ↔ ⊤
-- ν𝟏 = mk↔′
--   (λ { refl → tt })
--   (λ { tt → refl })
--   (λ { tt → refl })
--   (λ { refl → refl })
def null_emptystr {α: Type u}:
  @null α _ emptystr <=> PUnit :=
  TEquiv.mk
    (fun _ => PUnit.unit)
    (fun _ => trfl)
    (fun _ => trfl)
    (fun _ => trfl)

-- ν`  : ν (` c) ↔ ⊥
-- ν` = mk↔′ (λ ()) (λ ()) (λ ()) (λ ())
def null_char {α: Type u} {c: α}:
  null (char c) <=> PEmpty :=
  TEquiv.mk nofun nofun nofun nofun

-- ν∪  : ν (P ∪ Q) ≡ (ν P ⊎ ν Q)
-- ν∪ = refl
def null_or {α: Type u} {P Q: Lang α}:
  null (or P Q) ≡ (Sum (null P) (null Q)) :=
  trfl

-- ν∩  : ν (P ∩ Q) ≡ (ν P × ν Q)
-- ν∩ = refl
def null_and {α: Type u} {P Q: Lang α}:
  null (and P Q) ≡ (Prod (null P) (null Q)) :=
  trfl

-- ν·  : ν (s · P) ≡ (s × ν P)
-- ν· = refl
def null_scalar {α: Type u} {s: Type u} {P: Lang α}:
  null (scalar s P) ≡ (Prod s (null P)) :=
  trfl

-- ν⋆  : ν (P ⋆ Q) ↔ (ν P × ν Q)
-- ν⋆ = mk↔′
--   (λ { (([] , []) , refl , νP , νQ) → νP , νQ })
--   (λ { (νP , νQ) → ([] , []) , refl , νP , νQ })
--   (λ { (νP , νQ) → refl } )
--   (λ { (([] , []) , refl , νP , νQ) → refl})
def null_concat {α: Type u} {P Q: Lang α}:
  null (concat P Q) <=> (Prod (null P) (null Q)) := by
  refine TEquiv.mk ?toFun ?invFun ?leftInv ?rightInv
  case toFun =>
    intro ⟨x, y, hx, hy, hxy⟩
    simp at hxy
    simp [hxy] at hx hy
    exact ⟨hx, hy⟩
  case invFun =>
    exact fun ⟨x, y⟩ => ⟨[], [], x, y, rfl⟩
  case leftInv =>
    intro ⟨x, y, hx, hy, hxy⟩
    simp at hxy
    cases hxy.left with | refl =>
    cases hxy.right with | refl =>
    exact trfl
  case rightInv =>
    exact fun _ => trfl

-- ν✪  : ν (P ✪) ↔ (ν P) ✶
-- ν✪ {P = P} = mk↔′ k k⁻¹ invˡ invʳ
--  where
--    k : ν (P ✪) → (ν P) ✶
--    k zero✪ = []
--    k (suc✪ (([] , []) , refl , (νP , νP✪))) = νP ∷ k νP✪

--    k⁻¹ : (ν P) ✶ → ν (P ✪)
--    k⁻¹ [] = zero✪
--    k⁻¹ (νP ∷ νP✶) = suc✪ (([] , []) , refl , (νP , k⁻¹ νP✶))

--    invˡ : ∀ (νP✶ : (ν P) ✶) → k (k⁻¹ νP✶) ≡ νP✶
--    invˡ [] = refl
--    invˡ (νP ∷ νP✶) rewrite invˡ νP✶ = refl

--    invʳ : ∀ (νP✪ : ν (P ✪)) → k⁻¹ (k νP✪) ≡ νP✪
--    invʳ zero✪ = refl
--    invʳ (suc✪ (([] , []) , refl , (νP , νP✪))) rewrite invʳ νP✪ = refl

-- ν☆  : ν (P ☆) ↔ (ν P) ✶
-- ν☆ {P = P} =
--   begin
--     ν (P ☆)
--   ≈˘⟨ ✪↔☆ ⟩
--     ν (P ✪)
--   ≈⟨ ν✪ ⟩
--     (ν P) ✶
--   ∎ where open ↔R
def null_star {α: Type u} {P: Lang α}:
  null (star P) <=> List (null P) := by
  refine TEquiv.mk ?toFun ?invFun ?leftInv ?rightInv
  case toFun =>
    -- TODO: The proof is complicated enough in Agda to warrant the liberal use of tactics in Lean
    sorry
  case invFun =>
    -- TODO: The proof is complicated enough in Agda to warrant the liberal use of tactics in Lean
    sorry
  case leftInv =>
    -- TODO: The proof is complicated enough in Agda to warrant the liberal use of tactics in Lean
    sorry
  case rightInv =>
    -- TODO: The proof is complicated enough in Agda to warrant the liberal use of tactics in Lean
    sorry

-- δ∅  : δ ∅ a ≡ ∅
-- δ∅ = refl
def derive_emptyset {α: Type u} {a: α}:
  (derive emptyset a) ≡ emptyset :=
  trfl

-- δ𝒰  : δ 𝒰 a ≡ 𝒰
-- δ𝒰 = refl
def derive_universal {α: Type u} {a: α}:
  (derive universal a) ≡ universal :=
  trfl

-- δ𝟏  : δ 𝟏 a ⟷ ∅
-- δ𝟏 = mk↔′ (λ ()) (λ ()) (λ ()) (λ ())
def derive_emptystr {α: Type u} {a: α} {w: List α}:
  (derive emptystr a) w <=> emptyset w :=
  TEquiv.mk nofun nofun nofun nofun

-- δ`  : δ (` c) a ⟷ (a ≡ c) · 𝟏
-- δ` = mk↔′
--   (λ { refl → refl , refl })
--   (λ { (refl , refl) → refl })
--   (λ { (refl , refl) → refl })
--   (λ { refl → refl })
def derive_char {α: Type u} {a: α} {c: α} {w: List α}:
  (derive (char c) a) w <=> (scalar (a ≡ c) emptystr) w := by
  refine TEquiv.mk ?toFun ?invFun ?leftInv ?rightInv
  case toFun =>
    intro ⟨ D ⟩
    cases D with | refl =>
    exact ⟨ trfl, trfl ⟩
  case invFun =>
    intro ⟨ ⟨ H1 ⟩ , ⟨ H2 ⟩  ⟩
    cases H1 with | refl =>
    cases H2 with | refl =>
    exact trfl
  case leftInv =>
    intro ⟨ H ⟩
    cases H with | refl =>
    exact trfl
  case rightInv =>
    intro ⟨ ⟨ H1 ⟩, ⟨ H2 ⟩ ⟩
    cases H1 with | refl =>
    cases H2 with | refl =>
    exact trfl

-- δ∪  : δ (P ∪ Q) a ≡ δ P a ∪ δ Q a
-- δ∪ = refl
def derive_or {α: Type u} {a: α} {P Q: Lang α}:
  (derive (or P Q) a) ≡ (or (derive P a) (derive Q a)) :=
  trfl

-- δ∩  : δ (P ∩ Q) a ≡ δ P a ∩ δ Q a
-- δ∩ = refl
def derive_and {α: Type u} {a: α} {P Q: Lang α}:
  (derive (and P Q) a) ≡ (and (derive P a) (derive Q a)) :=
  trfl

-- δ·  : δ (s · P) a ≡ s · δ P a
-- δ· = refl
def derive_scalar {α: Type u} {a: α} {s: Type u} {P: Lang α}:
  (derive (scalar s P) a) ≡ (scalar s (derive P a)) :=
  trfl

-- δ⋆  : δ (P ⋆ Q) a ⟷ ν P · δ Q a ∪ δ P a ⋆ Q
-- δ⋆ {a = a} {w = w} = mk↔′
--   (λ { (([] , .(a ∷ w)) , refl , νP , Qaw) → inj₁ (νP , Qaw)
--      ; ((.a ∷ u , v) , refl , Pu , Qv) → inj₂ ((u , v) , refl , Pu , Qv) })
--   (λ { (inj₁ (νP , Qaw)) → ([] , a ∷ w) , refl , νP , Qaw
--      ; (inj₂ ((u , v) , refl , Pu , Qv)) → ((a ∷ u , v) , refl , Pu , Qv) })
--   (λ { (inj₁ (νP , Qaw)) → refl
--      ; (inj₂ ((u , v) , refl , Pu , Qv)) → refl })
--   (λ { (([] , .(a ∷ w)) , refl , νP , Qaw) → refl
--      ; ((.a ∷ u , v) , refl , Pu , Qv) → refl })
def derive_concat {α: Type u} {a: α} {P Q: Lang α} {w: List α}:
  (derive (concat P Q) a) w <=> (or (scalar (null P) (derive Q a)) (concat (derive P a) Q)) w := by
  refine TEquiv.mk ?toFun ?invFun ?leftInv ?rightInv
  case toFun =>
    -- TODO: The proof is complicated enough in Agda to warrant the liberal use of tactics in Lean
    sorry
  case invFun =>
    -- TODO: The proof is complicated enough in Agda to warrant the liberal use of tactics in Lean
    sorry
  case leftInv =>
    -- TODO: The proof is complicated enough in Agda to warrant the liberal use of tactics in Lean
    sorry
  case rightInv =>
    -- TODO: The proof is complicated enough in Agda to warrant the liberal use of tactics in Lean
    sorry

-- δ✪  : δ (P ✪) a ⟷ (ν P) ✶ · (δ P a ⋆ P ✪)
-- δ✪ {P}{a} {w} = mk↔′ k k⁻¹ invˡ invʳ
--  where
--    k : δ (P ✪) a w → ((ν P) ✶ · (δ P a ⋆ P ✪)) w
--    k (suc✪ (([] , .(a ∷ w)) , refl , (νP , P✪a∷w))) with k P✪a∷w
--    ... |            νP✶  , etc
--        = νP ∷ νP✶ , etc
--    k (suc✪ ((.a ∷ u , v) , refl , (Pa∷u , P✪v))) = [] , (u , v) , refl , (Pa∷u , P✪v)

--    k⁻¹ : ((ν P) ✶ · (δ P a ⋆ P ✪)) w → δ (P ✪) a w
--    k⁻¹ ([] , (u , v) , refl , (Pa∷u , P✪v)) = (suc✪ ((a ∷ u , v) , refl , (Pa∷u , P✪v)))
--    k⁻¹ (νP ∷ νP✶ , etc) = (suc✪ (([] , a ∷ w) , refl , (νP , k⁻¹ (νP✶ , etc))))

--    invˡ : (s : ((ν P) ✶ · (δ P a ⋆ P ✪)) w) → k (k⁻¹ s) ≡ s
--    invˡ ([] , (u , v) , refl , (Pa∷u , P✪v)) = refl
--    invˡ (νP ∷ νP✶ , etc) rewrite invˡ (νP✶ , etc) = refl

--    invʳ : (s : δ (P ✪) a w) → k⁻¹ (k s) ≡ s
--    invʳ (suc✪ (([] , .(a ∷ w)) , refl , (νP , P✪a∷w))) rewrite invʳ P✪a∷w = refl
--    invʳ (suc✪ ((.a ∷ u , v) , refl , (Pa∷u , P✪v))) = refl

-- δ☆  : δ (P ☆) a ⟷ (ν P) ✶ · (δ P a ⋆ P ☆)
-- δ☆ {P = P}{a} {w} =
--   begin
--     δ (P ☆) a w
--   ≈˘⟨ ✪↔☆ ⟩
--     δ (P ✪) a w
--   ≈⟨ δ✪ ⟩
--     ((ν P) ✶ · (δ P a ⋆ P ✪)) w
--   ≈⟨ ×-congˡ (⋆-congˡ ✪↔☆) ⟩
--     ((ν P) ✶ · (δ P a ⋆ P ☆)) w
--   ∎ where open ↔R
def derive_star {α: Type u} {a: α} {P: Lang α} {w: List α}:
  (derive (star P) a) w <=> (scalar (List (null P)) (concat (derive P a) (star P))) w := by
  refine TEquiv.mk ?toFun ?invFun ?leftInv ?rightInv
  case toFun =>
    -- TODO: The proof is complicated enough in Agda to warrant the liberal use of tactics in Lean
    sorry
  case invFun =>
    -- TODO: The proof is complicated enough in Agda to warrant the liberal use of tactics in Lean
    sorry
  case leftInv =>
    -- TODO: The proof is complicated enough in Agda to warrant the liberal use of tactics in Lean
    sorry
  case rightInv =>
    -- TODO: The proof is complicated enough in Agda to warrant the liberal use of tactics in Lean
    sorry

-- 𝒟′ : (A ✶ → B) → A ✶ → B × (A ✶ → B)
-- 𝒟′ f u = f u , 𝒟 f u
def derives' {α: Type u} {β: Type v} (f: List α -> β) (u: List α): (β × (List α -> β)) :=
  (f u, derives f u)

-- ʻ𝒟 : (A ✶ → B) → A ✶ → B × (A ✶ → B)
-- ʻ𝒟 f u = let f″ = foldl δ f u in ν f″ , f″
def derives'' {α: Type u} {β: Type v} (f: List α -> β) (u: List α): (β × (List α -> β)) :=
  let f' := foldl derive f u
  (null f', f')

-- 𝒟′≡ʻ𝒟 : 𝒟′ f ≗ ʻ𝒟 f
-- 𝒟′≡ʻ𝒟     []     = refl
-- 𝒟′≡ʻ𝒟 (a  ∷ as)  = 𝒟′≡ʻ𝒟 as
-- The paper says: "For functions f and g, f ≗ g is extensional equality, i.e., ∀ x → f x ≡ g x."
def derives'_is_derives'' {α: Type u} {β: Type v} (f: List α -> β):
  (w: List α) -> (derives' f w) ≡ (derives'' f w) :=
  fun w =>
  match w with
  | [] => trfl
  | (a :: as) =>
    by sorry
  -- TODO when trying to translate the Agda to Lean using:
  -- | (a :: as) => derives'_is_derives'' as
  -- We get the following type error:
  -- type mismatch
  --   derives'_is_derives'' as
  -- has type
  --   derives' f as ≡ derives'' f as : Type (max v u)
  -- but is expected to have type
  --   derives' f (a :: as) ≡ derives'' f (a :: as) : Type (max v u)

end Calculus
