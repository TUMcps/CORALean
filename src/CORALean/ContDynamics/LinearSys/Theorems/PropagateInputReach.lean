module

public import CORALean.ContDynamics.LinearSys.Operations.PropagateInputSolution
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationEq

@[expose] public section

/-!
# The propagation is exact on the exact particular solution

[1, Prop. 1] propagates its two approximations by `Z_S(t_{k+1}) = Z_S(t_k) ⊕
e^{A t_k} Z_S(Δt)`, and on the exact particular solution that recursion is an
equality rather than an enclosure: it is [2, Prop. 4] read at `a = Δt` and
`b = t_k`, the step being prepended rather than appended, which is what puts
`e^{A t_k}` on the one-step set instead of on the accumulated one.

`construct U` nonempty is what the base case needs — with no admissible input at
all there is no run, and `P_R(0)` is empty rather than `{0}`.

## Inputs
* `sys` – linear system
* `U` – input set
* `Δt` – step length
* `ω` – number of steps

## Hypotheses
* `hΔt` – step length nonnegative
* `hbdd` – input set bounded
* `hne` – input set nonempty

## Conclusion
* the propagated one-step reach is the exact reach over the horizon

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control, 2026.
* [2] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Over an empty window nothing is contributed, provided some input exists at
all to contribute it. -/
private theorem LinearSys.aux_inputReach_zero (sys : LinearSys 𝕋 n) {U : S n}
    (hne : (construct U).Nonempty) : -- --- CONCL ---
    sys.inputReach U 0 = {0} := by -- --- PROOF ---
  obtain ⟨c, hc⟩ := hne
  ext y
  constructor
  · rintro ⟨u, -, -, rfl⟩
    simp
  · rintro rfl
    exact ⟨fun _ => c, fun _ _ => hc, aestronglyMeasurable_const, by simp⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1]'s propagation, run on the exact particular solution over one
step, is the exact particular solution over the horizon. -/
theorem LinearSys.propagateInputSolution_inputReach (sys : LinearSys 𝕋 n) {U : S n} {Δt : ℝ}
    (hΔt : 0 ≤ Δt) (hbdd : Bornology.IsBounded (construct U))
    (hne : (construct U).Nonempty) (ω : ℕ) : -- --- CONCL ---
    sys.propagateInputSolution Δt (sys.inputReach U Δt) ω
      = sys.inputReach U ((ω : ℝ) * Δt) := by -- --- PROOF ---
  induction ω with
  | zero => simpa [LinearSys.propagateInputSolution] using
      (sys.aux_inputReach_zero hne).symm
  | succ k ih =>
    have hk : (0:ℝ) ≤ (k : ℝ) * Δt := mul_nonneg (Nat.cast_nonneg k) hΔt
    have hsep := sys.inputReach_separation_eq (U := U) hΔt hk hbdd
    have hcast : ((k + 1 : ℕ) : ℝ) * Δt = Δt + (k : ℝ) * Δt := by push_cast; ring
    rw [LinearSys.propagateInputSolution, ih, hcast, hsep, add_comm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
