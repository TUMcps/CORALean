module

public import CORALean.ContSet.InflatedContSet.Theorems.LinCombSubset
public import CORALean.ContSet.Interval.Float.Theorems.LinCombOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.LinCombNominalAt

@[expose] public section

/-!
# `PolyZonotope.linComb` contains every segment between the two sets

`InflatedContSet.linComb_subset` reduces this to two obligations: the nominal
parts spill only by what rounded, and the box absorbs that spill along with the
segment between the two incoming boxes.

The nominal obligation is the exact `linComb` argument — `2λ-1` on the fresh
factor, `pairCoeffSum` and `pairCoeffDiff` on the independent block — with the
centre, the sliding generator and the paired independent generators displaced.
No stored value is unfolded: each cancels against its own residual or against
`linCombGIDiff`, so what remains is the exact identity.

The three dependent blocks contribute nothing to the spill: halving and negation
are exact, and the monomials are exponent data over ℕ throughout, so both counts
are what they are over ℝ.

Only `_outer`, as over ℝ, and for the exact layer's reason rather than a
rounding one: the independent coefficients cannot be tied to the same `λ`.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   03-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem PolyZonotope.aux_linComb_nominal (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) :
    Set.linComb (nominalSet pZ₁) (nominalSet pZ₂) ⊆
      nominalSet (pZ₁.linComb pZ₂)
        + ((PolyZonotope.midpointResidual pZ₁.c pZ₂.c).construct
            + ((PolyZonotope.halfDiffError pZ₁.c pZ₂.c).construct
                + (Zonotope.generatorError
                    (PolyZonotope.linCombGIDiff pZ₁ pZ₂)).construct)) := by -- --- PROOF ---
  rintro _ ⟨y₁, hy₁', y₂, hy₂', lam, ⟨hl0, hl1⟩, rfl⟩
  obtain ⟨a₁, β₁, ha₁, hβ₁, hy₁⟩ := PolyZonotope.mem_nominalSet_iff.mp hy₁'
  obtain ⟨a₂, β₂, ha₂, hβ₂, hy₂⟩ := PolyZonotope.mem_nominalSet_iff.mp hy₂'
  obtain ⟨β, hβ, _, rfl, e, he, hx⟩ :=
    PolyZonotope.linComb_nominal_at pZ₁ pZ₂ (a₁ := a₁) (a₂ := a₂) hβ₁ hβ₂ hl0 hl1
  -- the nominal point at `[a₁; a₂; 2λ-1]`, every factor admissible
  refine ⟨_, PolyZonotope.mem_nominalSet_iff.mpr
    ⟨Fin.append (Fin.append a₁ a₂) (fun _ : Fin 1 => 2 * lam - 1), β, ?_, hβ, fun _ => rfl⟩,
    e, he, ?_⟩
  · refine Fin.addCases ?_ ?_
    · refine Fin.addCases ?_ ?_
      · intro k
        simpa using ha₁ k
      · intro k
        simpa using ha₂ k
    · intro _
      simp only [Fin.append_right]
      rw [abs_le]
      constructor <;> linarith
  · rw [hx, funext hy₁, funext hy₂]

/-- The box absorbs the two incoming boxes, both centre roundings and the
independent block's. -/
theorem PolyZonotope.aux_linComb_error (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) :
    Set.linComb pZ₁.I_error.construct pZ₂.I_error.construct
        + ((PolyZonotope.midpointResidual pZ₁.c pZ₂.c).construct
            + ((PolyZonotope.halfDiffError pZ₁.c pZ₂.c).construct
                + (Zonotope.generatorError
                    (PolyZonotope.linCombGIDiff pZ₁ pZ₂)).construct))
      ⊆ (pZ₁.linComb pZ₂).I_error.construct :=
  subset_trans
    (Set.add_subset_add (Interval.linComb_outer pZ₁.I_error pZ₂.I_error)
      (subset_trans (Set.add_subset_add_left (Interval.plus_outer _ _))
        (Interval.plus_outer _ _)))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.linComb_outer (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) :
    Set.linComb pZ₁.construct pZ₂.construct ⊆ (pZ₁.linComb pZ₂).construct :=
  InflatedContSet.linComb_subset (PolyZonotope.aux_linComb_nominal pZ₁ pZ₂)
    (PolyZonotope.aux_linComb_error pZ₁ pZ₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
