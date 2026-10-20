module

public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Taylm.Real.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.MonomialSingle
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# A box as an array of Taylor models

## Inputs
* `I` – interval
* `N` – Taylor order

## Hypotheses
* none

## Conclusion
* interval is contained in its Taylor model
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Through the box's zonotope, whose factors are the variables here. -/
theorem Interval.taylm_contains (I : Interval (Vec ℝ n)) (N : ℕ) :
    I.construct ⊆ Taylm.construct (I.taylm N) := by -- --- PROOF ---
  intro x hx
  obtain ⟨β, hβ, hxβ⟩ := I.zonotope_contains hx
  refine ⟨β, hβ, fun i => ?_⟩
  have hxi := congrFun hxβ i
  simp only [Interval.zonotope, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hxi
  simp only [Interval.taylm, Taylm.poly, Taylm.polyOf_cons, Taylm.polyOf_nil,
    Taylm.monomial_zero, Taylm.monomial_single]
  constructor <;> linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
