import CORALean.ContSet.Zonotope.Real.Operations.MatPow
import CORALean.ContSet.Zonotope.Real.Theorems.MatMulOuter
import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem

/-!
# Every power of a matrix the zonotope denotes lies in the zonotope's power

Induction on the exponent, `matMul_outer` at each step and `mem_ofPoint` at the
identity. `pow_succ'` is what matches `A ^ (k + 1) = A * A ^ k` to `matPow`'s
own recursion, which multiplies the base in on the left.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.matPow_outer (M : Zonotope (Mat ℝ n n)) {A : Mat ℝ n n}
    (hA : A ∈ M.construct) (k : ℕ) :
    A ^ k ∈ (M.matPow k).construct := by -- --- PROOF ---
  induction k with
  | zero =>
      rw [pow_zero]
      exact Zonotope.mem_ofPoint (1 : Mat ℝ n n)
  -- the previous power paired with the base itself, which is what `matMul` bounds
  | succ k ih =>
      have hmem : A * A ^ k ∈ (Zonotope.matMul M (M.matPow k)).construct :=
        Zonotope.matMul_outer M (M.matPow k) (Set.mem_biUnion hA ⟨A ^ k, ih, rfl⟩)
      rw [pow_succ']
      exact hmem

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
