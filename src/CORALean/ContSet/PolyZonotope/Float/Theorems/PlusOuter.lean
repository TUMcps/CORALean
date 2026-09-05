import CORALean.ContSet.InflatedContSet.Theorems.PlusSubset
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
import CORALean.ContSet.PolyZonotope.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet

/-!
# `PolyZonotope.plus` over-approximates the Minkowski sum

`InflatedContSet.plus_subset` reduces this to two obligations: the nominal parts
spill only by the centre rounding, and the box absorbs that spill along with the
two incoming boxes.

The nominal obligation is the exact `plus` argument with the centre displaced —
`Fin.append a₁ a₂` on the factors and `Fin.append β₁ β₂` on the independent
coefficients — and `monomial_plusE_left`/`_right` are what read a concatenated
factor vector back as each set's own. Nothing about the monomials rounds, so
this is a zonotope's `plus` with an extra block.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `plus`'s dependent generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem PolyZonotope.aux_sum_univ_plus_h {PZ₁ PZ₂ : PolyZonotope 𝕋 n}
    (f : Fin (PZ₁.h + PZ₂.h) → ℝ) :
    ∑ l : Fin (PZ₁.plus PZ₂).h, f l
      = ∑ l, f (Fin.castAdd PZ₂.h l) + ∑ l, f (Fin.natAdd PZ₁.h l) :=
  Fin.sum_univ_add f

omit [SoundFloatArithmetic 𝕋] in
/-- The same at the independent generator count. -/
theorem PolyZonotope.aux_sum_univ_plus_q {PZ₁ PZ₂ : PolyZonotope 𝕋 n}
    (f : Fin (PZ₁.q + PZ₂.q) → ℝ) :
    ∑ j : Fin (PZ₁.plus PZ₂).q, f j
      = ∑ j, f (Fin.castAdd PZ₂.q j) + ∑ j, f (Fin.natAdd PZ₁.q j) :=
  Fin.sum_univ_add f

/-- The concatenated blocks account for everything but the centre rounding. -/
theorem PolyZonotope.aux_plus_nominal (PZ₁ PZ₂ : PolyZonotope 𝕋 n) :
    nominalSet PZ₁ + nominalSet PZ₂ ⊆
      nominalSet (PZ₁.plus PZ₂) + (PolyZonotope.centerResidual PZ₁.c PZ₂.c).construct := by
  rintro _ ⟨x₁, hx₁', x₂, hx₂', rfl⟩
  obtain ⟨a₁, β₁, ha₁, hβ₁, hx₁⟩ := PolyZonotope.mem_nominalSet_iff.mp hx₁'
  obtain ⟨a₂, β₂, ha₂, hβ₂, hx₂⟩ := PolyZonotope.mem_nominalSet_iff.mp hx₂'
  refine ⟨fun i => toReal ((PZ₁.plus PZ₂).c i)
            + (∑ l, toReal ((PZ₁.plus PZ₂).G i l)
                * Real.PolyZonotope.monomial (PZ₁.plus PZ₂).E (Fin.append a₁ a₂) l)
            + ∑ j, toReal ((PZ₁.plus PZ₂).GI i j) * Fin.append β₁ β₂ j,
          PolyZonotope.mem_nominalSet_iff.mpr
            ⟨Fin.append a₁ a₂, Fin.append β₁ β₂, ?_, ?_, fun _ => rfl⟩,
          fun i => toReal (PZ₁.c i) + toReal (PZ₂.c i) - toReal ((PZ₁.plus PZ₂).c i), ?_, ?_⟩
  -- every appended factor and coefficient is admissible on the half it came from
  · refine Fin.addCases (fun k => ?_) (fun k => ?_)
    · simpa using ha₁ k
    · simpa using ha₂ k
  · refine Fin.addCases (fun j => ?_) (fun j => ?_)
    · simpa using hβ₁ j
    · simpa using hβ₂ j
  · exact Interval.sub_mem_residual (fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩)
  · funext i
    simp only [Pi.add_apply]
    rw [PolyZonotope.aux_sum_univ_plus_h, PolyZonotope.aux_sum_univ_plus_q]
    simp only [PolyZonotope.plus, Real.PolyZonotope.monomial_plusE_left,
      Real.PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right,
      hx₁ i, hx₂ i]
    ring

/-- The box absorbs the two incoming boxes and the centre rounding. -/
theorem PolyZonotope.aux_plus_error (PZ₁ PZ₂ : PolyZonotope 𝕋 n) :
    PZ₁.err.construct + PZ₂.err.construct
        + (PolyZonotope.centerResidual PZ₁.c PZ₂.c).construct ⊆
      (PZ₁.plus PZ₂).err.construct :=
  subset_trans (Set.add_subset_add_right (Interval.plus_outer PZ₁.err PZ₂.err))
    (Interval.plus_outer _ _)

theorem PolyZonotope.plus_outer (PZ₁ PZ₂ : PolyZonotope 𝕋 n) :
    PZ₁.construct + PZ₂.construct ⊆ (PZ₁.plus PZ₂).construct :=
  InflatedContSet.plus_subset (PolyZonotope.aux_plus_nominal PZ₁ PZ₂)
    (PolyZonotope.aux_plus_error PZ₁ PZ₂)

end CORALean.Float
