module

public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemConstructIffOfEq

@[expose] public section

/-!
# A polynomial level set of equations on the unit box, over a floating-point scalar

Where every row is `=` and the stored box is `[-1, 1]ⁿ`, a point is in the set exactly when every
coordinate has modulus at most `1` and every row is met to within its slack: [1, Def. 7]'s
`constrDom` with the float layer's slack, the factors of a float constrained polynomial zonotope.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Equations on the stored unit box: a point is in the cube and meets each row within its slack. -/
theorem PolyLevelSet.mem_construct_iff_of_eq_unit {P : PolyLevelSet 𝕋 n} (h : ∀ i, P.op i = .eq)
    (hD : P.dom = Interval.unit n) {x : Vec ℝ n} : x ∈ P.construct
      ↔ (∀ k, |x k| ≤ 1) ∧ ∀ i, |(toRealMat P.A *ᵥ Real.PolyZonotope.monomial P.R x) i
        - toReal (P.b i)| ≤ |toReal (P.b_error i)| := by
  rw [PolyLevelSet.mem_construct_iff_of_eq h, hD, Interval.mem_unit_iff]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
