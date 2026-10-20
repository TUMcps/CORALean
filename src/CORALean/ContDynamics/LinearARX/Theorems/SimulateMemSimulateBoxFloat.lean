module

public import CORALean.ContDynamics.LinearARX.Operations.SimulateBoxFloat
public import CORALean.ContDynamics.LinearARX.Theorems.FeedMemFeedBox
public import CORALean.ContDynamics.LinearARX.Theorems.StackSimulateZero
public import CORALean.ContDynamics.LinearARX.Theorems.ToLinearSysDTStep
public import CORALean.ContDynamics.LinearSysDT.Theorems.MemSimulateBoxIn

@[expose] public section

/-!
# The real ARX run lies in the float boxes

The window `stack` of `simulate` from the real value of a float start window under
the real values of a float input signal lies, at every step, in `simulateBox`
computed in float arithmetic: the float `simulate` row's guarantee (ruling R-SIM).
An enclosure, so the box is outer.

## Inputs
* `sys` – ARX system
* `y₀` – float start window
* `u` – float input signal
* `k` – step

## Hypotheses
* none

## Conclusion
* the real run's window lies in the float box
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar ContSet CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {dy du p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.simulate_mem_simulateBox (sys : LinearARX 𝕋 dy du p) (y₀ : Vec 𝕋 (p * dy))
    (u : ℕ → Vec 𝕋 du) (k : ℕ) : -- --- CONCL ---
    LinearARX.stack p (sys.simulate (Scalar.toRealVec y₀) fun j => Scalar.toRealVec (u j)) k ∈
      construct (sys.simulateBox y₀ u k) := by -- --- PROOF ---
  -- the ARX recursion for `k ≥ p` is `simulate`'s definition
  have hrec : ∀ k, p ≤ k →
      sys.simulate (Scalar.toRealVec y₀) (fun j => Scalar.toRealVec (u j)) k
        = ∑ i : Fin p, Scalar.toRealMat (sys.Abar i) *ᵥ
              sys.simulate (Scalar.toRealVec y₀) (fun j => Scalar.toRealVec (u j)) (k - (i + 1))
          + ∑ j : Fin (p + 1), Scalar.toRealMat (sys.Bbar j) *ᵥ Scalar.toRealVec (u (k - j)) :=
    fun k hk => by rw [LinearARX.simulate, dif_neg (not_lt.mpr hk)]
  -- the first window is the start window
  have h0 : LinearARX.stack p
      (sys.simulate (Scalar.toRealVec y₀) fun j => Scalar.toRealVec (u j)) 0 ∈
        construct (Interval.point y₀) := by
    rw [LinearARX.stack_simulate_zero]
    exact Interval.mem_point y₀
  -- so the stacked windows take the converted system's step
  have hstep : ∀ k, LinearARX.stack p
        (sys.simulate (Scalar.toRealVec y₀) fun j => Scalar.toRealVec (u j)) (k + 1)
      = Scalar.toRealMat sys.toLinearSysDT.A *ᵥ LinearARX.stack p
          (sys.simulate (Scalar.toRealVec y₀) fun j => Scalar.toRealVec (u j)) k
        + sys.feed (fun j => Scalar.toRealVec (u j)) k :=
    fun k => sys.toLinearSysDT_step
      (y := sys.simulate (Scalar.toRealVec y₀) fun j => Scalar.toRealVec (u j))
      (u := fun j => Scalar.toRealVec (u j)) hrec k
  -- the feed lies in the feed box; then the generic box induction
  have hu := fun k => sys.feed_mem_feedBox u k
  exact sys.toLinearSysDT.mem_simulateBoxIn (Interval.point y₀) (sys.feedBox u) h0 hu hstep k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
