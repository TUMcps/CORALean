module

public import CORALean.ContDynamics.LinearSys.Definitions.BackReachSetExistsForallExact
public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormZero
public import CORALean.ContDynamics.LinearSys.Theorems.MemExpNegImageIff
public import CORALean.ContDynamics.LinearSys.Theorems.IsPerturbedTrajectoryClosedForm
public import CORALean.ContDynamics.LinearSys.Theorems.PerturbedSuperposition

@[expose] public section

/-!
# [1, Prop. 5]: the time-point EA backward reachable set, exactly

`R^{∃∀}(-t) = e^{-At}((Xend ⊖ Z_W(t)) ⊕ -Z_U(t))`, at the exact particular solutions
`inputReach U t` and `inputReach W t`, plain sets of points, so the identity is the one the paper
states "independently of the set representations chosen". The same superposition step as [1, Prop.
3] carries it, with the quantifiers the other way round: the chosen input is the witness `-c` the
outer `⊕ -Z_U(t)` supplies, and the erosion `Xend ⊖ Z_W(t)` is exactly "lands in `Xend` whatever the
disturbance contributes". Nothing is cancelled off the Minkowski difference anywhere, which would
make the argument unsound.

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
* the set is the propagated eroded target plus the negated input solution

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

/-- [1, Prop. 5]: the states some admissible input steers into `Xend` despite
every disturbance are exactly `e^{-At}((Xend ⊖ Z_W(t)) ⊕ -Z_U(t))`. -/
theorem LinearSys.backReachSetExistsForallExact_eq (sys : LinearSys 𝕋 n) (U W Xend : S n)
    {t : ℝ} (ht : 0 ≤ t) (hU : Bornology.IsBounded (construct U))
    (hW : Bornology.IsBounded (construct W)) : -- --- CONCL ---
    sys.backReachSetExistsForallExact (Set.Icc 0 t) U W Xend t
      = (exp ((-t) • toRealMat sys.A)).mulVecLin ''
          (minkowskiDiff (construct Xend) (sys.inputReach W t)
            + -sys.inputReach U t) := by -- --- PROOF ---
  ext x₀
  rw [mem_expNeg_image_iff]
  constructor
  · -- the chosen input's own integral is the `-Z_U(t)` summand, up to sign
    rintro ⟨u, hu, humeas, hall⟩
    rw [Set.mem_add]
    refine ⟨exp (t • toRealMat sys.A) *ᵥ x₀
      + ∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s, ?_,
      -(∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s), ?_, by abel⟩
    · rintro _ ⟨w, hw, hwmeas, rfl⟩
      obtain ⟨x, traj, hx0, hxt⟩ := hall w hw hwmeas
      have hsup := traj.superposition ht hU hW
      rw [hx0] at hsup
      rwa [← hsup]
    · rw [Set.mem_neg, neg_neg]
      exact ⟨u, hu, humeas, rfl⟩
  · -- conversely, the `-Z_U(t)` summand names the input that works for every `w`
    rintro h
    obtain ⟨y, hy, c, hc, hyc⟩ := Set.mem_add.mp h
    rw [Set.mem_neg] at hc
    obtain ⟨u, hu, humeas, hcu⟩ := hc
    refine ⟨u, hu, humeas, fun w hw hwmeas => ?_⟩
    have traj := sys.isPerturbedTrajectory_closedForm ht hU hW x₀ hu humeas hw hwmeas
    have hx0 : sys.closedForm x₀ u 0 + sys.closedForm 0 w 0 = x₀ := by
      rw [sys.closedForm_zero, sys.closedForm_zero, add_zero]
    have hsup := traj.superposition ht hU hW
    rw [hx0] at hsup
    refine ⟨fun τ => sys.closedForm x₀ u τ + sys.closedForm 0 w τ, traj, hx0, ?_⟩
    -- the input's integral cancels `c`, leaving the eroded point plus the disturbance
    have hsum : exp (t • toRealMat sys.A) *ᵥ x₀
        + (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s)
        + (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ w s)
        = y + ∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ w s := by
      rw [← hyc, ← hcu]
      abel
    have hend : sys.closedForm x₀ u t + sys.closedForm 0 w t
        = y + ∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ w s := by
      rw [hsup]; exact hsum
    show sys.closedForm x₀ u t + sys.closedForm 0 w t ∈ construct Xend
    rw [hend]
    exact hy _ ⟨w, hw, hwmeas, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
