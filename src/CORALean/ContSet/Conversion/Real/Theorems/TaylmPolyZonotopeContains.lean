module

public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import CORALean.ContSet.Taylm.Real.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Conversion.Real.Operations.Taylm_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Theorems.TaylmDepApply
public import CORALean.ContSet.Conversion.Real.Theorems.TaylmIndepApply
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# An array of Taylor models as a polynomial zonotope

`Taylm.polyZonotope_contains`: its `polyZonotope` contains it.

## Inputs
* `T` – Taylor models, one per coordinate

## Hypotheses
* none

## Conclusion
* Taylor models are contained in their polynomial zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.polyZonotope_contains (T : Fin m → Taylm n) : -- --- CONCL ---
    Taylm.construct T ⊆ (Taylm.polyZonotope T).construct := by -- --- PROOF ---
  rintro x ⟨t, ht, hx⟩
  -- the remainder values form a point of the remainder box, which its zonotope reaches
  set R : Interval (Vec ℝ m) := ⟨fun i => (T i).rem.inf, fun i => (T i).rem.sup⟩
  have hR : (fun i => x i - (T i).poly t) ∈ R.construct := fun i => hx i
  obtain ⟨β, hβ, hxβ⟩ := R.zonotope_contains hR
  refine ⟨t, β, ht, hβ, funext fun i => ?_⟩
  have hxi := congrFun hxβ i
  simp only [Interval.zonotope, R, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hxi
  rw [Pi.add_apply, Pi.add_apply, Taylm.dep_apply]
  have h3 := Taylm.indep_apply T β i
  erw [h3]
  simp only [Taylm.polyZonotope]
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
