module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Mtimes
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Ellipsoid.mtimesCost`

Asserted, not proved: `Operations/Mtimes.lean` sends the shape vector `q` and
each of the `k` generator columns through one matrix-vector product at
`m × n`, `M *ᵥ ·` and `M * E.G` being the same operation column by column.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Ellipsoid.mtimes` costs at `M : Mat ℝ m n` and `k` generators: one
matrix-vector product for `q` and one per generator column. -/
def Ellipsoid.mtimesCost (m n k : ℕ) : Cost := (k + 1) • Cost.matVec m n

/-- Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost. -/
theorem Ellipsoid.mtimesCost_mono {k k' : ℕ} (m n : ℕ) (hle : k ≤ k') :
    Ellipsoid.mtimesCost m n k ≤ Ellipsoid.mtimesCost m n k' :=
  Nat.mul_le_mul_right _ (Nat.succ_le_succ hle)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
