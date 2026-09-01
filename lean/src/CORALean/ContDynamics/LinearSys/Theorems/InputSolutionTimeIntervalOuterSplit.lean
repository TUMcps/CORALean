import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionTimeIntervalOuter

/-!
# A time-interval input enclosure when the input set misses the origin

Althoff's second case. `inputSolution_timeInterval_outer` needs `0 ∈ U`, and
when that fails the thesis splits the input set into a constant `ũ` and a set
`Ũ` that does contain the origin, encloses each contribution separately, and
adds them.

The split is a hypothesis rather than an operation: `ContSet` offers no way to
name a centre, so which `c` and which `U₀` is the representation's business. A
zonotope has both for free — its centre and itself recentred.

## What this does not reproduce

The thesis encloses the constant part by interpolating its exact solution,
`x̃_p(t) ∈ (t/r) x̃_p(r) ⊕ F̃ũ` with `F̃ = A⁻¹F`, which is tighter than treating
`ũ` as one more uncertain input. Here the constant part goes through
`inputSolution` at a set `U₁` holding both `0` and `c`, which is sound but
looser: it allows every input in that set at every time, where the thesis knows
the input never moves.

Reproducing `F̃` needs the Taylor form of `∫₀ᵗ e^{Aσ} dσ`, whose tail is an
integrated matrix series — and bounding that tail by `Ê(r)` rather than `2Ê(r)`
needs the terms integrated one by one, which is the same single-series argument
`CorrectionMatrix` documents. This project has no machinery for integrating a
matrix power series termwise, so that enclosure is not available yet.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) n] [OuterContSet S ℝ]

set_option maxHeartbeats 1000000 in
/-- The input's contribution over any time in the step, split along
`U ⊆ {c} ⊕ U₀`: the constant `c` enclosed at `U₁`, the rest at `U₀`, and the two
added. Neither piece needs `0 ∈ U`; both need the origin in the set that
encloses them. -/
theorem LinearSys.Trajectory.inputSolution_timeInterval_outer_split [Mtimes IntervalMat S]
    {sys : LinearSys 𝕋 n} {R₀ U U₀ U₁ : S n} {x u : ℝ → Vec ℝ n} {c : Vec ℝ n} {r : ℝ}
    (traj : sys.Trajectory R₀ U x u) (hr : 0 < r) (η : ℕ)
    (hε : ‖r • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1)
    -- the split
    (hsplit : ∀ y ∈ construct U, y - c ∈ construct U₀)
    (hc : c ∈ construct U₁)
    (h0₀ : (0 : Vec ℝ n) ∈ construct U₀) (h0₁ : (0 : Vec ℝ n) ∈ construct U₁)
    -- what Thm. 3.1 asks of each piece
    (hconv₀ : Convex ℝ (construct U₀)) (hclosed₀ : IsClosed (construct U₀))
    (hbdd₀ : Bornology.IsBounded (construct U₀))
    (hRconv₀ : Convex ℝ (construct (Mtimes.mtimes
      (IntervalMat.inputRemainder (toRealMat sys.A) r η) U₀)))
    (hRclosed₀ : IsClosed (construct (Mtimes.mtimes
      (IntervalMat.inputRemainder (toRealMat sys.A) r η) U₀)))
    (hRbdd₀ : Bornology.IsBounded (construct (Mtimes.mtimes
      (IntervalMat.inputRemainder (toRealMat sys.A) r η) U₀)))
    (hconv₁ : Convex ℝ (construct U₁)) (hclosed₁ : IsClosed (construct U₁))
    (hbdd₁ : Bornology.IsBounded (construct U₁))
    (hRconv₁ : Convex ℝ (construct (Mtimes.mtimes
      (IntervalMat.inputRemainder (toRealMat sys.A) r η) U₁)))
    (hRclosed₁ : IsClosed (construct (Mtimes.mtimes
      (IntervalMat.inputRemainder (toRealMat sys.A) r η) U₁)))
    (hRbdd₁ : Bornology.IsBounded (construct (Mtimes.mtimes
      (IntervalMat.inputRemainder (toRealMat sys.A) r η) U₁)))
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s)
      ∈ construct (OuterContSet.plus (sys.inputSolution r η U₁)
          (sys.inputSolution r η U₀)) := by
  set A := toRealMat sys.A with hA
  -- the two pieces, each admissible for its own set
  have hmem₁ : ∀ s ∈ Set.Icc (0:ℝ) t, (fun _ : ℝ => c) s ∈ construct U₁ := fun _ _ => hc
  have hmem₀ : ∀ s ∈ Set.Icc (0:ℝ) t, (fun σ => u σ - c) s ∈ construct U₀ :=
    fun s hs => hsplit _ (traj.input s hs.1)
  have hmeas₀ : AEStronglyMeasurable (fun σ => u σ - c)
      (volume.restrict (Set.Icc 0 t)) :=
    (traj.aestronglyMeasurable_input le_rfl).sub aestronglyMeasurable_const
  have hint₁ := aux_intervalIntegrable_input (A := A) (c := t) ht0 hbdd₁ hmem₁
    aestronglyMeasurable_const
  have hint₀ := aux_intervalIntegrable_input (A := A) (c := t) ht0 hbdd₀ hmem₀ hmeas₀
  -- linearity splits the integral the same way
  have hsum : (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
      = (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ c)
        + ∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ (u s - c) := by
    rw [← intervalIntegral.integral_add hint₁ hint₀]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [← Matrix.mulVec_add]
    congr 1
    abel
  rw [hsum]
  refine OuterContSet.plus_outer _ _ (Set.add_mem_add ?_ ?_)
  · exact sys.inputReach_subset_inputSolution hr η hε hconv₁ hclosed₁ hbdd₁
      hRconv₁ hRclosed₁ hRbdd₁
      (sys.inputReach_mono hbdd₁ h0₁ ht0 htr
        ⟨fun _ => c, hmem₁, aestronglyMeasurable_const, rfl⟩)
  · exact sys.inputReach_subset_inputSolution hr η hε hconv₀ hclosed₀ hbdd₀
      hRconv₀ hRclosed₀ hRbdd₀
      (sys.inputReach_mono hbdd₀ h0₀ ht0 htr ⟨fun σ => u σ - c, hmem₀, hmeas₀, rfl⟩)

end CORALean.Real
