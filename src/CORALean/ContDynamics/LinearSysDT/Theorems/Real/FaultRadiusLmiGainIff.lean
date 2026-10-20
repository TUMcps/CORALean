module

public import CORALean.ContDynamics.LinearSysDT.Definitions.FaultRadiusLmiGain
public import CORALean.ContDynamics.LinearSysDT.Definitions.FaultRadiusLmi

@[expose] public section

/-!
# The two forms of the P-radius inequality agree

[1, Eq. 16], [1, Eq. 17]: for a symmetric `P`, the inequality with the gain `L`
(`LinearSysDT.FaultRadiusLmiGain`) is the inequality of Eq. 17 (`LinearSysDT.FaultRadiusLmi`) at
`W = PL`, the same matrix: `(A - LC)ᵀP = AᵀP - CᵀWᵀ` and `(LD_yH_v)ᵀP = H_vᵀD_yᵀWᵀ`, as
`Wᵀ = LᵀP` for a symmetric `P`.

## Inputs
* `A` – state matrix
* `C` – output matrix
* `Dx` – disturbance matrix
* `Hw` – disturbance generators
* `Dy` – noise matrix
* `Hv` – noise generators
* `P` – Lyapunov matrix
* `L` – observer gain
* `γ` – radius bound

## Hypotheses
* `hP` – Lyapunov matrix symmetric

## Conclusion
* the inequalities with the gain and with the product agree

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

variable {n ny nw nv rw rv : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.faultRadiusLmiGain_iff (A : Mat ℝ n n) (C : Mat ℝ ny n) (Dx : Mat ℝ n nw)
    (Hw : Mat ℝ nw rw) (Dy : Mat ℝ ny nv) (Hv : Mat ℝ nv rv) (P : Mat ℝ n n) (L : Mat ℝ n ny)
    (γ : ℝ) (hP : Pᵀ = P) : -- --- CONCL ---
    LinearSysDT.FaultRadiusLmiGain A C Dx Hw Dy Hv P L γ ↔
      LinearSysDT.FaultRadiusLmi A C Dx Hw Dy Hv P (P * L) γ := by -- --- PROOF ---
  -- the last column of the two matrices is the same, `Wᵀ = LᵀP`
  have hW : (P * L)ᵀ = Lᵀ * P := by rw [transpose_mul, hP]
  have h1 : (A - L * C)ᵀ * P = Aᵀ * P - Cᵀ * (P * L)ᵀ := by
    rw [hW, transpose_sub, transpose_mul, Matrix.sub_mul, Matrix.mul_assoc]
  have h2 : (L * (Dy * Hv))ᵀ * P = (Dy * Hv)ᵀ * (P * L)ᵀ := by
    rw [hW, transpose_mul, Matrix.mul_assoc]
  unfold LinearSysDT.FaultRadiusLmiGain LinearSysDT.FaultRadiusLmi
  simp only [h1, h2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
