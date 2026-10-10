import CORALean.ContSet.PolyZonotope.Real.Operations.SquareExample
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The square example is the interval `[0, 1]`

`{α² | α ∈ [-1, 1]} = [0, 1]`: a square lies in `[0, 1]` there, and `√x` is the factor reaching `x`.
So the set is a polytope although it has an exponent of two, which CORA's `isPolytope` [1] takes
as proof that it is not (FINDINGS.md).

## References

* [1] `contSet/@polyZonotope/isPolytope.m`, CORA (Sep. 2025), by N. Kochdumper (2019).
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.squareExample_construct :
    PolyZonotope.squareExample.construct =
      (Interval.mk (fun _ => 0) (fun _ => 1)).construct := by -- --- PROOF ---
  ext x
  constructor
  · -- a square of a factor in `[-1, 1]` is in `[0, 1]`
    rintro ⟨a, β, ha, -, hx⟩ i
    have h1 := abs_le.mp (ha (0 : Fin 1))
    subst hx
    simp [PolyZonotope.squareExample, PolyZonotope.monomial]
    show (0 : ℝ) ≤ (a (0 : Fin 1) ^ 2 • (fun _ : Fin 1 => (1 : ℝ))) i ∧
      (a (0 : Fin 1) ^ 2 • (fun _ : Fin 1 => (1 : ℝ))) i ≤ 1
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    constructor <;> nlinarith [h1.1, h1.2]
  · -- `√x` is the factor
    intro hx
    have h0 : (0 : ℝ) ≤ x 0 := (hx 0).1
    have h1 : x 0 ≤ (1 : ℝ) := (hx 0).2
    refine ⟨fun _ => Real.sqrt (x 0), Fin.elim0, fun _ => ?_, fun j => Fin.elim0 j, ?_⟩
    · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_one.mpr h1
    · funext i
      simp [PolyZonotope.squareExample, PolyZonotope.monomial, Real.sq_sqrt h0]
      fin_cases i
      rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
