module

public import CORALean.ContDynamics.LinearSys.Definitions.BackReachSetForallExistsExact
public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormZero
public import CORALean.ContDynamics.LinearSys.Theorems.MemExpNegImageIff
public import CORALean.ContDynamics.LinearSys.Theorems.IsPerturbedTrajectoryClosedForm
public import CORALean.ContDynamics.LinearSys.Theorems.PerturbedSuperposition

@[expose] public section

/-!
# [1, Prop. 3]: the time-point AE backward reachable set, exactly

`R^{∀∃}(-t) = e^{-At}((Xend ⊕ -Z_W(t)) ⊖ Z_U(t))`, with `Z_U` and `Z_W` the exact particular
solutions `inputReach U t` and `inputReach W t`, plain sets of points. Superposition turns the
quantifiers over *signals* into quantifiers over *points* of those two sets, in both directions:
every point of `inputReach` is some admissible signal's integral, and every admissible signal's
integral is a point of it. The remaining step is the adjunction `{y} ⊕ Z_U ⊆ S ↔ y ∈ S ⊖ Z_U`, read
off `minkowskiDiff`'s definition, and no summand is ever cancelled off a Minkowski difference. The
paper defers its proof to a discrete-time predecessor; the argument here is direct, and needs `U`
and `W` bounded, which the paper's zonotopes are.

## Inputs
* `sys` – linear system
* `U` – input set
* `W` – disturbance set
* `Xend` – target set
* `t` – target time

## Hypotheses
* `ht` – time nonnegative
* `hU` – input set bounded
* `hW` – disturbance set bounded

## Conclusion
* the set is the propagated target plus the negated disturbance solution, eroded by the input

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 3]: the states no admissible input keeps out of `Xend` are exactly
`e^{-At}((Xend ⊕ -Z_W(t)) ⊖ Z_U(t))`. -/
theorem LinearSys.backReachSetForallExistsExact_eq (sys : LinearSys 𝕋 n) (U W Xend : S n)
    {t : ℝ} (ht : 0 ≤ t) (hU : Bornology.IsBounded (construct U))
    (hW : Bornology.IsBounded (construct W)) : -- --- CONCL ---
    sys.backReachSetForallExistsExact (Set.Icc 0 t) U W Xend t
      = (exp ((-t) • toRealMat sys.A)).mulVecLin ''
          minkowskiDiff (construct Xend + -sys.inputReach W t)
            (sys.inputReach U t) := by -- --- PROOF ---
  ext x₀
  rw [mem_expNeg_image_iff]
  constructor
  · -- every point of `Z_U(t)` is some admissible signal's integral, so the run exists
    intro hx₀ p hp
    obtain ⟨u, hu, humeas, rfl⟩ := hp
    obtain ⟨w, x, traj, hx0, hxt⟩ := hx₀ u hu humeas
    have hsup := traj.superposition ht hU hW
    rw [hx0] at hsup
    rw [Set.mem_add]
    refine ⟨x t, hxt, -(∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ w s), ?_, ?_⟩
    · rw [Set.mem_neg, neg_neg]
      exact ⟨w, traj.disturbance, traj.measDisturbance, rfl⟩
    · rw [hsup]; abel
  · -- conversely, the disturbance the adjunction hands back is realized by a run
    intro hx₀ u hu humeas
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp
      (hx₀ _ (⟨u, hu, humeas, rfl⟩ : _ ∈ sys.inputReach U t))
    rw [Set.mem_neg] at hb
    obtain ⟨w, hw, hwmeas, hqb⟩ := hb
    have traj := sys.isPerturbedTrajectory_closedForm ht hU hW x₀ hu humeas hw hwmeas
    have hx0 : sys.closedForm x₀ u 0 + sys.closedForm 0 w 0 = x₀ := by
      rw [sys.closedForm_zero, sys.closedForm_zero, add_zero]
    have hsup := traj.superposition ht hU hW
    rw [hx0] at hsup
    refine ⟨w, fun τ => sys.closedForm x₀ u τ + sys.closedForm 0 w τ, traj, hx0, ?_⟩
    -- the endpoint is the target point the adjunction produced, `b` cancelling `∫ w`
    have hsum : exp (t • toRealMat sys.A) *ᵥ x₀
        + (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s)
        + (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ w s) = a := by
      have hbeq : b = -(∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ w s) := by
        rw [← hqb, neg_neg]
      rw [← hab, hbeq]
      abel
    have hend : sys.closedForm x₀ u t + sys.closedForm 0 w t = a := by rw [hsup]; exact hsum
    show sys.closedForm x₀ u t + sys.closedForm 0 w t ∈ construct Xend
    rw [hend]
    exact ha

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
