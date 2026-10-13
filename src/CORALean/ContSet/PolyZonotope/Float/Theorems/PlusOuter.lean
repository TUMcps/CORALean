module

public import CORALean.ContSet.InflatedContSet.Theorems.PlusSubset
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.PolyZonotope.Float.Operations.Plus
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet

@[expose] public section

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

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [SoundFloatArithmetic 𝕋] in
/-- `Fin.sum_univ_add` at `plus`'s dependent generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem PolyZonotope.aux_sum_univ_plus_h {pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)}
    (f : Fin (pZ₁.h + pZ₂.h) → ℝ) :
    ∑ l : Fin (pZ₁.plus pZ₂).h, f l
      = ∑ l, f (Fin.castAdd pZ₂.h l) + ∑ l, f (Fin.natAdd pZ₁.h l) :=
  Fin.sum_univ_add f

omit [SoundFloatArithmetic 𝕋] in
/-- The same at the independent generator count. -/
theorem PolyZonotope.aux_sum_univ_plus_q {pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)}
    (f : Fin (pZ₁.q + pZ₂.q) → ℝ) :
    ∑ j : Fin (pZ₁.plus pZ₂).q, f j
      = ∑ j, f (Fin.castAdd pZ₂.q j) + ∑ j, f (Fin.natAdd pZ₁.q j) :=
  Fin.sum_univ_add f

/-- The concatenated blocks account for everything but the centre rounding. -/
theorem PolyZonotope.aux_plus_nominal (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) :
    nominalSet pZ₁ + nominalSet pZ₂ ⊆
      nominalSet (pZ₁.plus pZ₂)
        + (PolyZonotope.centerResidual pZ₁.c pZ₂.c).construct := by -- --- PROOF ---
  rintro _ ⟨x₁, hx₁', x₂, hx₂', rfl⟩
  obtain ⟨a₁, β₁, ha₁, hβ₁, hx₁⟩ := PolyZonotope.mem_nominalSet_iff.mp hx₁'
  obtain ⟨a₂, β₂, ha₂, hβ₂, hx₂⟩ := PolyZonotope.mem_nominalSet_iff.mp hx₂'
  refine ⟨fun i => toReal ((pZ₁.plus pZ₂).c i)
            + (∑ l, toReal ((pZ₁.plus pZ₂).G l i)
                * Real.PolyZonotope.monomial (pZ₁.plus pZ₂).E (Fin.append a₁ a₂) l)
            + ∑ j, toReal ((pZ₁.plus pZ₂).GI j i) * Fin.append β₁ β₂ j,
          PolyZonotope.mem_nominalSet_iff.mpr
            ⟨Fin.append a₁ a₂, Fin.append β₁ β₂, ?_, ?_, fun _ => rfl⟩,
          fun i => toReal (pZ₁.c i) + toReal (pZ₂.c i) - toReal ((pZ₁.plus pZ₂).c i), ?_, ?_⟩
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
theorem PolyZonotope.aux_plus_error (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) :
    pZ₁.err.construct + pZ₂.err.construct
        + (PolyZonotope.centerResidual pZ₁.c pZ₂.c).construct ⊆
      (pZ₁.plus pZ₂).err.construct :=
  subset_trans (Set.add_subset_add_right (Interval.plus_outer pZ₁.err pZ₂.err))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.plus_outer (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) :
    pZ₁.construct + pZ₂.construct ⊆ (pZ₁.plus pZ₂).construct :=
  InflatedContSet.plus_subset (PolyZonotope.aux_plus_nominal pZ₁ pZ₂)
    (PolyZonotope.aux_plus_error pZ₁ pZ₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
