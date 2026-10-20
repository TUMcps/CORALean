module

public import CORALean.ContDynamics.LinearSysDT.Operations.SimulateBoxIn

@[expose] public section

/-!
# A run through the boxes stays in the boxes

Any real sequence that starts in `B₀` and steps by `x(k+1) = A x(k) + u(k)` with
`u(k)` in the `k`-th input box stays in the `k`-th box of `simulateBoxIn`. Both
the point run (`simulate_mem_simulateBox`) and the ARX window run use it.

## Inputs
* `sys` – system
* `B₀` – start box
* `U` – input boxes per step
* `x` – states
* `u` – inputs
* `k` – step

## Hypotheses
* `h₀` – start lies in `B₀`
* `hu` – inputs lie in their boxes
* `hstep` – the step recursion holds

## Conclusion
* the state at step `k` lies in the `k`-th box
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar Plus Mtimes ContSet CORALean.Float

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.mem_simulateBoxIn (sys : LinearSysDT 𝕋 n) (B₀ : Interval (Vec 𝕋 n))
    (U : ℕ → Interval (Vec 𝕋 n)) {x u : ℕ → Vec ℝ n} (h₀ : x 0 ∈ construct B₀)
    (hu : ∀ k, u k ∈ construct (U k))
    (hstep : ∀ k, x (k + 1) = Scalar.toRealMat sys.A *ᵥ x k + u k) (k : ℕ) : -- --- CONCL ---
    x k ∈ construct (sys.simulateBoxIn B₀ U k) := by -- --- PROOF ---
  induction k with
  | zero => exact h₀
  | succ k ih =>
    rw [hstep k]
    exact plus_outer (S := Interval (Vec 𝕋 n)) _ _
      (Set.add_mem_add (mtimes_outer (S := ℐ𝒱[𝕋]) sys.A _
        (Set.mem_biUnion rfl (Set.mem_image_of_mem _ ih))) (hu k))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
