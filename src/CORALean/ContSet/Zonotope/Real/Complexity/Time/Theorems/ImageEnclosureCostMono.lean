module

public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.PlusCost
public import CORALean.ContSet.Zonotope.Real.Operations.ImageEnclosure
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ImageEnclosureCost

@[expose] public section

/-!
# `Zonotope.imageEnclosureCost_mono`

Monotone in the generator count.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the generator count. -/
theorem Zonotope.imageEnclosureCost_mono {q q' : ℕ} (n : ℕ) (cNeuron : Cost) (hq : q ≤ q') :
    Zonotope.imageEnclosureCost n q cNeuron ≤
      Zonotope.imageEnclosureCost n q' cNeuron := by -- --- PROOF ---
  simp only [Cost.le_iff, Zonotope.imageEnclosureCost, Zonotope.mtimesCost, Cost.ops_add,
    Cost.ops_smul]
  have : 2 * (n * (q + 1)) ≤ 2 * (n * (q' + 1)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  have : (q + 1) * (Cost.matVec n n).ops ≤ (q' + 1) * (Cost.matVec n n).ops :=
    Nat.mul_le_mul_right _ (by omega)
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
