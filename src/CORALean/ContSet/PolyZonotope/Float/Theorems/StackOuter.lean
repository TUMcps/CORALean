module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Stack
public import CORALean.ContSet.PolyZonotope.Float.Theorems.BlockPadLeftNominal
public import CORALean.ContSet.PolyZonotope.Float.Theorems.BlockPadRightNominal
public import CORALean.ContSet.PolyZonotope.Float.Theorems.ExactPlusOuter
public import CORALean.ContSet.PolyZonotope.Real.Operations.Stack

@[expose] public section

/-!
# `PolyZonotope.stack` over-approximates the stack of the two sets

The padded sets denote the exact layer's padded nominal sets (`nominal_blockPadLeft`,
`nominal_blockPadRight`), so the exact `stack` of the two nominal sets, plus the two error boxes
padded the same way, is `exactPlus_outer` at the padded pair: the factors the two sets share stay
shared, and only the center sum rounds. Outer, not exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n n₁ n₂ : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A box point padded below by zero is a point of the padded box. -/
theorem PolyZonotope.aux_padLeft_err (pZ : PolyZonotope (Vec 𝕋 n)) (n₂ : ℕ) :
    CORALean.blockPadLeft n n₂ '' pZ.I_error.construct ⊆
      (pZ.blockPadLeft n₂).I_error.construct := by -- --- PROOF ---
  rintro _ ⟨e, he, rfl⟩ i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · show toReal (Fin.append pZ.I_error.inf (fun _ => (zero : 𝕋)) (Fin.castAdd n₂ i)) ≤
        Fin.append e 0 (Fin.castAdd n₂ i) ∧ Fin.append e 0 (Fin.castAdd n₂ i) ≤
        toReal (Fin.append pZ.I_error.sup (fun _ => (zero : 𝕋)) (Fin.castAdd n₂ i))
    simp only [Fin.append_left]
    exact he i
  · show toReal (Fin.append pZ.I_error.inf (fun _ => (zero : 𝕋)) (Fin.natAdd n i)) ≤
        Fin.append e 0 (Fin.natAdd n i) ∧ Fin.append e 0 (Fin.natAdd n i) ≤
        toReal (Fin.append pZ.I_error.sup (fun _ => (zero : 𝕋)) (Fin.natAdd n i))
    simp only [Fin.append_right, toReal_zero]
    exact ⟨le_refl _, le_refl _⟩

/-- A box point padded above by zero is a point of the padded box. -/
theorem PolyZonotope.aux_padRight_err (pZ : PolyZonotope (Vec 𝕋 n)) (n₁ : ℕ) :
    CORALean.blockPadRight n₁ n '' pZ.I_error.construct ⊆
      (pZ.blockPadRight n₁).I_error.construct := by -- --- PROOF ---
  rintro _ ⟨e, he, rfl⟩ i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · show toReal (Fin.append (fun _ => (zero : 𝕋)) pZ.I_error.inf (Fin.castAdd n i)) ≤
        Fin.append 0 e (Fin.castAdd n i) ∧ Fin.append 0 e (Fin.castAdd n i) ≤
        toReal (Fin.append (fun _ => (zero : 𝕋)) pZ.I_error.sup (Fin.castAdd n i))
    simp only [Fin.append_left, toReal_zero]
    exact ⟨le_refl _, le_refl _⟩
  · show toReal (Fin.append (fun _ => (zero : 𝕋)) pZ.I_error.inf (Fin.natAdd n₁ i)) ≤
        Fin.append 0 e (Fin.natAdd n₁ i) ∧ Fin.append 0 e (Fin.natAdd n₁ i) ≤
        toReal (Fin.append (fun _ => (zero : 𝕋)) pZ.I_error.sup (Fin.natAdd n₁ i))
    simp only [Fin.append_right]
    exact he i


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.stack_outer (pZ₁ : PolyZonotope (Vec 𝕋 n₁)) (pZ₂ : PolyZonotope (Vec 𝕋 n₂))
    (hp : pZ₁.p = pZ₂.p) : -- --- CONCL ---
    (Real.PolyZonotope.stack (nominal pZ₁) (nominal pZ₂) hp).construct
        + (CORALean.blockPadLeft n₁ n₂ '' pZ₁.I_error.construct
          + CORALean.blockPadRight n₁ n₂ '' pZ₂.I_error.construct)
      ⊆ (pZ₁.stack pZ₂ hp).construct := by -- --- PROOF ---
  have h := PolyZonotope.exactPlus_outer (pZ₁.blockPadLeft n₂) (pZ₂.blockPadRight n₁) hp
  -- the padded nominal sets are the exact layer's maps; the factor-list proof is carried along
  have key : ∀ (A B : Real.PolyZonotope (Vec ℝ (n₁ + n₂)))
      (_ : nominal (pZ₁.blockPadLeft n₂) = A) (_ : nominal (pZ₂.blockPadRight n₁) = B)
      (hAB : A.p = B.p),
      Real.PolyZonotope.exactPlus (nominal (pZ₁.blockPadLeft n₂))
        (nominal (pZ₂.blockPadRight n₁)) hp = Real.PolyZonotope.exactPlus A B hAB := by
    intro A B hA hB hAB
    subst hA
    subst hB
    rfl
  rw [key _ _ (PolyZonotope.nominal_blockPadLeft n₂ pZ₁)
    (PolyZonotope.nominal_blockPadRight n₁ pZ₂) hp] at h
  exact subset_trans (Set.add_subset_add_left (Set.add_subset_add
    (PolyZonotope.aux_padLeft_err pZ₁ n₂) (PolyZonotope.aux_padRight_err pZ₂ n₁))) h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
