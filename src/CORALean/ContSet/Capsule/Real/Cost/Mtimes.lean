import CORALean.ContSet.Capsule.Real.Operations.Mtimes
import CORALean.Global.Cost

/-!
# `Capsule.mtimesCost`

Asserted, not proved: `Operations/Mtimes.lean` computes the Frobenius norm of
`M` (`m * n` products, `m * n` additions, one `sqrt`), sends the centre and the
generator through `M *ᵥ ·` (two `Cost.matVec m n`) and scales the radius (one
product): `6 * m * n + 2`.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Capsule.mtimes` costs at `M : Mat ℝ m n`. -/
def Capsule.mtimesCost (m n : ℕ) : Cost := ⟨2 * (m * n) + 1⟩ + (2 : ℕ) • Cost.matVec m n + ⟨1⟩

/-- Monotone in both dimensions. -/
theorem Capsule.mtimesCost_mono {m m' n n' : ℕ} (hm : m ≤ m') (hn : n ≤ n') :
    Capsule.mtimesCost m n ≤ Capsule.mtimesCost m' n' := by
  have := Nat.mul_le_mul hm hn
  simp only [Capsule.mtimesCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul, Cost.matVec]
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
