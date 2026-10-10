import CORALean.ContSet.Zonotope.Real.Operations.QuadMap
import CORALean.Global.Cost

/-!
# `Zonotope.quadMapCost`

Asserted, not proved: `Operations/QuadMap.lean` at `Q : Fin m → Mat ℝ n n` and
`h` generators evaluates, per output coordinate, a bilinear form `xᵀ Q y`
(`Cost.matVec n n` plus a dot product, `2 * n * n + 2 * n`) for the centre term
(`h + 1` of them), twice for each of the `h` linear terms, once for each of the
`h` squared terms and twice for each of the `h * h` index pairs, with `O(1)`
additions or scalings around each. Summed, that is at most
`m * (h + 1)^2 * (4 * n * n + 4 * n + 2)`; the count is the plain polynomial,
the squared-terms and pair-terms share counted at the pair rate.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.quadMap` costs at `Q : Fin m → Mat ℝ n n` and `h` generators. -/
def Zonotope.quadMapCost (m n h : ℕ) : Cost := ⟨m * ((h + 1) ^ 2 * (4 * (n * n) + 4 * n + 2))⟩

/-- Monotone in the generator count. -/
theorem Zonotope.quadMapCost_mono {h h' : ℕ} (m n : ℕ) (hh : h ≤ h') :
    Zonotope.quadMapCost m n h ≤ Zonotope.quadMapCost m n h' :=
  Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.succ_le_succ hh) 2))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
