import CORALean.ContDynamics.LinearSys.Definitions.IsCanonicalForm

/-!
# The system `canonicalForm` returns is in canonical form [1]

`(A, I, 0, C, 0, 0, 0, I)`: `B = I`, `c = k = 0`, `E = 0`, `D = 0` and `F = I`, `n` inputs,
`r` noises. `canonicalForm` returns `A` and `(C, 0)` and these matrices are fixed by it.

## References

* [1] `contDynamics/@linearSys/isCanonicalForm.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.isCanonicalForm_canonical :
    LinearSys.IsCanonicalForm (1 : Mat ℝ n n) 0 (0 : Mat ℝ r n) 0 (0 : Mat ℝ n n)
      (1 : Mat ℝ r r) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun i j => ?_⟩
  -- the identity matrix against the value test
  rw [Matrix.one_apply]
  simp only [Fin.ext_iff]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
