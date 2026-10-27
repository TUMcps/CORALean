module

public import CORALean.ContDynamics.LinearSysDT.Definitions.IsHMinusLmiGain
public import CORALean.ContDynamics.LinearSysDT.Definitions.IsHMinusLmi

@[expose] public section

/-!
# The two forms of the `H₋` inequality agree

[1, Eq. 26], [1, Eq. 27]: with `Y = MᵀM`, `Q = αP` and `W = PL`, the inequality with the gain
(`LinearSysDT.IsHMinusLmiGain`) is the inequality of Eq. 27 (`LinearSysDT.IsHMinusLmi`), the same
matrix: `QA - QLC = αPA - αWC`, `-QLE = -αWE` and `-Q - CᵀMᵀMC = -αP - CᵀYC`.

## Inputs
* `A` – state matrix
* `C` – output matrix
* `E` – fault matrix
* `L` – observer gain
* `P` – Lyapunov matrix
* `M` – residual weight
* `α` – scaling
* `β` – sensitivity level

## Hypotheses
* none

## Conclusion
* the gain form and the weighted form of the inequality agree

## References

* [1] [Y. Wang, M. Zhou, V. Puig, G. Cembrano and Z. Wang. "Zonotopic Fault Detection Observer with
      H₋ Performance". 2017 36th Chinese Control Conference (CCC),
      2017.](../../../../../../references/2017/wang-ccc-fault-detection-observer.md)
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

theorem LinearSysDT.isHMinusLmiGain_iff_isHMinusLmi (A : Mat ℝ n n) (C : Mat ℝ ny n)
    (E : Mat ℝ ny nf) (L : Mat ℝ n ny) (P : Mat ℝ n n) (M : Mat ℝ ny ny) (α β : ℝ) :
    LinearSysDT.IsHMinusLmiGain A C E L (α • P) M β ↔
      LinearSysDT.IsHMinusLmi A C E P (P * L) (Mᵀ * M) α β := by
  unfold LinearSysDT.IsHMinusLmiGain LinearSysDT.IsHMinusLmi
  simp only [Matrix.smul_mul, Matrix.mul_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
