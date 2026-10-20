module

public import CORALean.ContDynamics.LinearSys.Theorems.ReachSetExactEq
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationEq

@[expose] public section

/-!
# Reaching `t + r` is reaching `t`, then flowing for `r`

The identity [1]'s proof of Theorem 1 runs on, `R_[ir,(i+1)r](I) = Φ_r(R_[(i-1)r,ir](I))`,
at one time: `Φ_{t+r}(R₀) = e^{rA}Φ_t(R₀) + inputReach U r`. Both sides in closed form
(`reachSetExact_eq`), it is the input reach set's separation
(`inputReach_separation_eq`) and `e^{(t+r)A} = e^{rA}e^{tA}`.

## Inputs
* `sys` – linear system
* `R₀` – initial set
* `U` – input set
* `t` – first time
* `r` – second time

## Hypotheses
* `ht` – first time nonnegative
* `hr` – second time nonnegative
* `hU` – input set bounded

## Conclusion
* the later reach set is the propagated earlier one plus the input reach

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid
      Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `Φ_{t+r}(R₀) = e^{rA}Φ_t(R₀) + inputReach U r`: [1, Thm. 1]'s step from one time interval
to the next, at one time. -/
theorem LinearSys.reachSetExact_add_eq (sys : LinearSys 𝕋 n) (R₀ U : S n) {t r : ℝ}
    (ht : 0 ≤ t) (hr : 0 ≤ r) (hU : Bornology.IsBounded (construct U)) : -- --- CONCL ---
    sys.reachSetExact (Set.Icc 0 (t + r)) R₀ U (t + r)
      = (fun y => exp (r • toRealMat sys.A) *ᵥ y) ''
          sys.reachSetExact (Set.Icc 0 t) R₀ U t + sys.inputReach U r := by -- --- PROOF ---
  have hmul : exp ((t + r) • toRealMat sys.A)
      = exp (r • toRealMat sys.A) * exp (t • toRealMat sys.A) := by
    rw [add_smul, add_comm]
    exact exp_add_of_commute (((Commute.refl (toRealMat sys.A)).smul_left r).smul_right t)
  rw [sys.reachSetExact_eq R₀ U (add_nonneg ht hr) hU, sys.reachSetExact_eq R₀ U ht hU,
    sys.inputReach_separation_eq ht hr hU]
  ext y
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, _, ⟨_, ⟨v, hv, rfl⟩, w, hw, rfl⟩, rfl⟩
    refine ⟨exp (r • toRealMat sys.A) *ᵥ (exp (t • toRealMat sys.A) *ᵥ z + v),
      ⟨_, ⟨_, ⟨z, hz, rfl⟩, v, hv, rfl⟩, rfl⟩, w, hw, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_add, Matrix.mulVec_mulVec, hmul]
    abel
  · rintro ⟨_, ⟨_, ⟨_, ⟨z, hz, rfl⟩, v, hv, rfl⟩, rfl⟩, w, hw, rfl⟩
    refine ⟨_, ⟨z, hz, rfl⟩, _, ⟨_, ⟨v, hv, rfl⟩, w, hw, rfl⟩, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_add, Matrix.mulVec_mulVec, hmul]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
