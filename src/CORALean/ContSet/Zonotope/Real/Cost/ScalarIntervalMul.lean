import CORALean.ContSet.Zonotope.Real.Operations.ScalarIntervalMul
import CORALean.ContSet.Zonotope.Real.Cost.Mtimes
import CORALean.ContSet.Zonotope.Real.Cost.Plus
import CORALean.ContSet.Zonotope.Real.Cost.UnitIntervalMul

/-!
# `Zonotope.scalarIntervalMulCost`

Asserted, not proved, by reading `Operations/ScalarIntervalMul.lean` as written:
the midpoint and half-width of `[a, b]` (two operations each), two
`Zonotope.mtimes` by a scalar multiple of the identity, applied as the dense
matrices they are, a `plus` and a `unitIntervalMul`. A caller who multiplies by
a scalar directly would pay less, which is not what this definition does.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.scalarIntervalMul` costs at `Vec ℝ n` and `h` generators. -/
def Zonotope.scalarIntervalMulCost (n h : ℕ) : Cost :=
  ⟨4⟩ + (2 : ℕ) • Zonotope.mtimesCost n n h + Zonotope.plusCost n + Zonotope.unitIntervalMulCost

/-- Monotone in the generator count. -/
theorem Zonotope.scalarIntervalMulCost_mono {h h' : ℕ} (n : ℕ) (hh : h ≤ h') :
    Zonotope.scalarIntervalMulCost n h ≤ Zonotope.scalarIntervalMulCost n h' := by
  have := Zonotope.mtimesCost_mono n n hh
  simp only [Zonotope.scalarIntervalMulCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul] at this ⊢
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
