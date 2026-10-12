import CORALean.ContDynamics.NonlinDASys.Operations.AbstractionErrorAdaptive
import CORALean.ContDynamics.NonlinDASys.Theorems.LinErrorOuter

/-!
# `abstractionErrorAdaptive` holds the Lagrange remainder

For every deviation `ν` in `dz` and Hessian rows in their intervals, half the quadratic forms
are in the errors `priv_abstractionError_adaptive` returns: `½ σ` in `Z_error_x`, `½ φ` in
`Z_error_y`, `½ (σ - CF⁻¹ φ)` in `Z_error`, the sign of the linearized DAE ([1, Cor. 1]). All
three are `NonlinDASys.linError_outer`, at `CF⁻¹ = 0` for the parts (CORA's tuning).

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix ContSet

variable {n p m q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The three errors of `abstractionErrorAdaptive` hold the quadratic forms of any Hessian rows
in the intervals, at any `ν` in `dz`. -/
theorem NonlinDASys.abstractionErrorAdaptive_outer (CF_inv : Mat ℝ n p)
    (H : NonlinDASys.HessData n p q) {Hd : Fin n → Mat ℝ q q} {Ha : Fin p → Mat ℝ q q}
    (hHd : ∀ i j k, |Hd i j k - H.Hd_c i j k| ≤ H.Hd_Δ i j k)
    (hHa : ∀ i j k, |Ha i j k - H.Ha_c i j k| ≤ H.Ha_Δ i j k) {ν : Vec ℝ q}
    (hν : ν ∈ H.dz.construct) :
    (1 / 2 : ℝ) • (fun i => ν ⬝ᵥ (Hd i *ᵥ ν))
        ∈ (NonlinDASys.abstractionErrorAdaptive CF_inv H).Z_error_x.construct ∧
      (1 / 2 : ℝ) • (fun j => ν ⬝ᵥ (Ha j *ᵥ ν))
        ∈ (NonlinDASys.abstractionErrorAdaptive CF_inv H).Z_error_y.construct ∧
      (1 / 2 : ℝ) • ((fun i => ν ⬝ᵥ (Hd i *ᵥ ν)) - CF_inv *ᵥ (fun j => ν ⬝ᵥ (Ha j *ᵥ ν)))
        ∈ (NonlinDASys.abstractionErrorAdaptive CF_inv H).Z_error.construct := by -- --- PROOF ---
  refine ⟨?_, ?_, NonlinDASys.linError_outer H.Hd_c H.Hd_Δ H.Ha_c H.Ha_Δ CF_inv H.dz hHd hHa hν⟩
  · have := NonlinDASys.linError_outer H.Hd_c H.Hd_Δ H.Ha_c H.Ha_Δ (0 : Mat ℝ n p) H.dz hHd hHa hν
    simpa [NonlinDASys.abstractionErrorAdaptive, Matrix.zero_mulVec] using this
  · have := NonlinDASys.linError_outer (n := p) (p := 0) H.Ha_c H.Ha_Δ Fin.elim0 Fin.elim0
      (0 : Mat ℝ p 0) H.dz (Hd := Ha) (Ha := Fin.elim0) hHa (fun i => i.elim0) hν
    simpa [NonlinDASys.abstractionErrorAdaptive, Matrix.zero_mulVec] using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
