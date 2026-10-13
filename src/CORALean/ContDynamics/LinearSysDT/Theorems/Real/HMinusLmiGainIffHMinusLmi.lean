import CORALean.ContDynamics.LinearSysDT.Definitions.HMinusLmiGain
import CORALean.ContDynamics.LinearSysDT.Definitions.HMinusLmi

/-!
# The two forms of the `H₋` inequality agree

[1, Eq. 26], [1, Eq. 27]: with `Y = MᵀM`, `Q = αP` and `W = PL`, the inequality with the gain
(`LinearSysDT.HMinusLmiGain`) is the inequality of Eq. 27 (`LinearSysDT.HMinusLmi`), the same
matrix: `QA - QLC = αPA - αWC`, `-QLE = -αWE` and `-Q - CᵀMᵀMC = -αP - CᵀYC`.

## References

* [1] Y. Wang, M. Zhou, V. Puig, G. Cembrano and Z. Wang. "Zonotopic Fault Detection Observer
      with H− Performance". In Proc. of the 36th Chinese Control Conference (CCC),
      pp. 7230-7235, 2017.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n ny nf : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.hMinusLmiGain_iff_hMinusLmi (A : Mat ℝ n n) (C : Mat ℝ ny n)
    (E : Mat ℝ ny nf) (L : Mat ℝ n ny) (P : Mat ℝ n n) (M : Mat ℝ ny ny) (α β : ℝ) :
    LinearSysDT.HMinusLmiGain A C E L (α • P) M β ↔
      LinearSysDT.HMinusLmi A C E P (P * L) (Mᵀ * M) α β := by
  unfold LinearSysDT.HMinusLmiGain LinearSysDT.HMinusLmi
  simp only [Matrix.smul_mul, Matrix.mul_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
