module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Plus
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.InflatedContSet.Theorems.PlusSubset
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemCartProdIff

@[expose] public section

/-!
# `ConPolyZono.plus` over-approximates the Minkowski sum

`PolyZonotope.plus_outer`'s argument at one more field, carried across the
layer by `PolyLevelSet.mem_cartProd_iff`. Only the center rounds, so the box holds the two
incoming boxes and one `centerResidual`, and all five counts are the exact
layer's.

## Inputs
* `cPZ₁` – first summand
* `cPZ₂` – second summand

## Hypotheses
* none

## Conclusion
* the Minkowski sum is contained in the result
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `plus`'s dependent generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem ConPolyZono.aux_sum_univ_plus_h {cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)}
    (f : Fin (cPZ₁.h + cPZ₂.h) → ℝ) :
    ∑ l : Fin (cPZ₁.plus cPZ₂).h, f l
      = ∑ l, f (Fin.castAdd cPZ₂.h l) + ∑ l, f (Fin.natAdd cPZ₁.h l) :=
  Fin.sum_univ_add f

omit [SoundFloatArithmetic 𝕋] in
/-- The same at the independent generator count. -/
theorem ConPolyZono.aux_sum_univ_plus_qI {cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)}
    (f : Fin (cPZ₁.qI + cPZ₂.qI) → ℝ) :
    ∑ j : Fin (cPZ₁.plus cPZ₂).qI, f j
      = ∑ j, f (Fin.castAdd cPZ₂.qI j) + ∑ j, f (Fin.natAdd cPZ₁.qI j) :=
  Fin.sum_univ_add f

theorem ConPolyZono.aux_plus_nominal (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    nominalSet cPZ₁ + nominalSet cPZ₂ ⊆
      nominalSet (cPZ₁.plus cPZ₂)
        + (PolyZonotope.centerResidual cPZ₁.c cPZ₂.c).construct := by -- --- PROOF ---
  rintro _ ⟨x₁, hx₁', x₂, hx₂', rfl⟩
  obtain ⟨a₁, β₁, ha₁, hβ₁, hs₁, hx₁⟩ := ConPolyZono.mem_nominalSet_iff.mp hx₁'
  obtain ⟨a₂, β₂, ha₂, hβ₂, hs₂, hx₂⟩ := ConPolyZono.mem_nominalSet_iff.mp hx₂'
  have hA₁ : (fun k => Fin.append a₁ a₂ (Fin.castAdd cPZ₂.p k)) = a₁ :=
    funext fun k => Fin.append_left a₁ a₂ k
  have hA₂ : (fun k => Fin.append a₁ a₂ (Fin.natAdd cPZ₁.p k)) = a₂ :=
    funext fun k => Fin.append_right a₁ a₂ k
  -- the witness: one appended factor vector, one appended coefficient vector
  refine ⟨fun i => toReal ((cPZ₁.plus cPZ₂).c i)
            + (∑ l, toReal ((cPZ₁.plus cPZ₂).G l i)
                * Real.PolyZonotope.monomial (cPZ₁.plus cPZ₂).E (Fin.append a₁ a₂) l)
            + ∑ j, toReal ((cPZ₁.plus cPZ₂).GI j i) * Fin.append β₁ β₂ j,
          ConPolyZono.mem_nominalSet_iff.mpr
            ⟨Fin.append a₁ a₂, Fin.append β₁ β₂, ?_, ?_, ?_, fun _ => rfl⟩,
          fun i => toReal (cPZ₁.c i) + toReal (cPZ₂.c i) - toReal ((cPZ₁.plus cPZ₂).c i), ?_, ?_⟩
  · refine Fin.addCases (fun k => ?_) (fun k => ?_)
    · simpa using ha₁ k
    · simpa using ha₂ k
  · refine Fin.addCases (fun j => ?_) (fun j => ?_)
    · simpa using hβ₁ j
    · simpa using hβ₂ j
  -- the constraint side, each system read on the factors it came with
  · refine (PolyLevelSet.mem_cartProd_iff cPZ₁.cons cPZ₂.cons _).mpr ⟨?_, ?_⟩
    · rw [hA₁]; exact hs₁
    · rw [hA₂]; exact hs₂
  · exact Interval.sub_mem_residual (fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩)
  · funext i
    simp only [Pi.add_apply]
    rw [ConPolyZono.aux_sum_univ_plus_h, ConPolyZono.aux_sum_univ_plus_qI]
    simp only [ConPolyZono.plus, Real.PolyZonotope.monomial_plusE_left,
      Real.PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right,
      hx₁ i, hx₂ i]
    ring

/-- The box absorbs the two incoming boxes and the center rounding. -/
theorem ConPolyZono.aux_plus_error (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    cPZ₁.I_error.construct + cPZ₂.I_error.construct
        + (PolyZonotope.centerResidual cPZ₁.c cPZ₂.c).construct ⊆
            (cPZ₁.plus cPZ₂).I_error.construct :=
  subset_trans (Set.add_subset_add_right (Interval.plus_outer cPZ₁.I_error cPZ₂.I_error))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.plus_outer (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    cPZ₁.construct + cPZ₂.construct ⊆ (cPZ₁.plus cPZ₂).construct :=
  InflatedContSet.plus_subset (ConPolyZono.aux_plus_nominal cPZ₁ cPZ₂)
    (ConPolyZono.aux_plus_error cPZ₁ cPZ₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
