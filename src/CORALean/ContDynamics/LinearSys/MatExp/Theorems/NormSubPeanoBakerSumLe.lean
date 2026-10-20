module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsPeanoBakerExpansion

@[expose] public section

/-!
# The Peano–Baker series truncated at order `η`, and what it leaves

A solution of `x(s) = x(0) + ∫₀ˢ A(σ) x(σ) dσ` on `[0, t]`, with every `A(σ)` in
the box `B`, differs from its first `η + 1` Peano–Baker terms applied to `x(0)`
by at most `‖x(0)‖` times `expRemainderBound` at the box of the step `t • B` —
the tail `MatExp.expIntervalEnclosure` already pays for a constant member.

`MatExp.exists_peanoBaker_expansion` at the zero input, whose terms all vanish.

`Vec` carries the sup norm, and `‖A(σ)‖` is the `l∞` operator norm it induces.

## Inputs
* `B` – interval matrix
* `A` – time-varying matrix
* `x` – run
* `t` – time
* `η` – Taylor order

## Hypotheses
* `hA` – matrix entries integrable
* `hAB` – matrix stays in the box
* `ht` – time nonnegative
* `hxc` – run continuous on the interval
* `hx` – run solves the integral equation
* `hε` – scaled norm small enough for the Taylor order

## Conclusion
* the run is its truncated Peano–Baker series up to the remainder bound
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   02-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run inside `B` is its first `η + 1` Peano–Baker terms applied to `x(0)`,
to within `‖x(0)‖` times the remainder bound at the box of the step. -/
theorem MatExp.norm_sub_peanoBakerSum_le {B : Interval (Mat ℝ n n)} {A : ℝ → Mat ℝ n n}
    (hA : ∀ i j a b, IntervalIntegrable (fun s => A s i j) volume a b)
    (hAB : ∀ s, A s ∈ B.construct)
    {x : ℝ → Vec ℝ n} {t : ℝ} (ht : 0 ≤ t) (hxc : ContinuousOn x (Set.Icc 0 t))
    (hx : ∀ s ∈ Set.Icc 0 t, x s = x 0 + ∫ σ in (0:ℝ)..s, A σ *ᵥ x σ) (η : ℕ)
    (hε : ‖(Interval.smul t B).absMax‖ / ((η : ℝ) + 2) < 1) : -- --- CONCL ---
    ‖x t - ∑ k ∈ Finset.range (η + 1), MatExp.peanoBakerTerm A k t *ᵥ x 0‖
      ≤ ‖x 0‖ * MatExp.expRemainderBound (Interval.smul t B).absMax η := by -- --- PROOF ---
  have h0 : ∀ k s, MatExp.peanoBakerInputTerm A (fun _ => (0 : Vec ℝ n)) k s = 0 := by
    intro k
    induction k with
    | zero => intro s; simp [MatExp.peanoBakerInputTerm]
    | succ k ih => intro s; simp [MatExp.peanoBakerInputTerm, ih]
  -- the expansion at the zero input, whose own remainder is zero too
  obtain ⟨ρh, ρu, hρh, hρu, heq⟩ := MatExp.exists_peanoBaker_expansion hA hAB
    (u := fun _ => 0) (fun _ _ => intervalIntegrable_const) ht hxc
    (fun s hs => by simpa using hx s hs) (ν := 0) (fun _ _ => by simp) η hε
  have hρu0 : ρu = 0 := norm_le_zero_iff.mp (by simpa using hρu)
  rw [heq, hρu0]
  simp only [h0, Finset.sum_const_zero, add_zero, add_sub_cancel_left]
  exact hρh

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
