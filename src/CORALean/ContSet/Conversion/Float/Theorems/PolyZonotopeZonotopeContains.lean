module

public import CORALean.ContSet.Conversion.Float.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope

@[expose] public section

/-!
# A polynomial zonotope as a zonotope, over a floating-point scalar

Every dependent factor's monomial lies in `[-1,1]`, so it is read as a free factor
of a zonotope, the dependent generators and then the independent ones; the error
box is carried across. Nothing rounds, and the exponents are dropped, which is
what makes this an enclosure rather than the set. A constrained polynomial
zonotope goes through its polynomial zonotope, as over ℝ.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* set is contained in its zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.zonotope_contains (pZ : PolyZonotope (Vec 𝕋 n)) :
    pZ.construct ⊆ pZ.zonotope.construct := by -- --- PROOF ---
  refine mono_subset (fun x hx => ?_) subset_rfl
  obtain ⟨a, β, ha, hβ, hx⟩ := PolyZonotope.mem_nominalSet_iff.mp hx
  refine Zonotope.mem_nominalSet_iff.mpr
    ⟨Fin.append (Real.PolyZonotope.monomial pZ.E a) β, ?_, fun i => ?_⟩
  · refine Fin.addCases (fun l => ?_) fun j => ?_
    · simpa using Real.PolyZonotope.abs_monomial_le_one pZ.E ha l
    · simpa using hβ j
  · rw [hx i]
    show _ = toReal (pZ.c i) + ∑ l : Fin (pZ.h + pZ.q),
      toReal (Fin.append pZ.G pZ.GI l i) * _
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
