module

public import CORALean.ContDynamics.LinearSys.Operations.ParticularSolution
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution
public import CORALean.ContDynamics.LinearSys.Theorems.PropagateInputReach
public import CORALean.ContDynamics.LinearSys.Theorems.PropagateInputSolutionMono
public import CORALean.ContSet.ContSet.Definitions.Interfaces
public import CORALean.ContSet.ContSet.Theorems.Basic

@[expose] public section

/-!
# `particularSolution` holds everything the input contributes by a window's end

Four steps, each proved on its own already. With `0 ∈ U`, the input reach set grows with time, as
the proof of [1, Prop. 4] has it, so every `t ≤ t_{k+1}` is bounded by `P^R(t_{k+1})`; that set is
exactly the one-step set propagated `k + 1` times [1, Prop. 4]; propagation preserves enclosure, and
[2, Prop. 2] encloses the one step in `inputSolution`; and the recursion `particularSolution`
computes encloses that propagation, one `plus` and one `mtimes` per window.

## Inputs
* `sys` – linear system
* `Δt` – step length
* `η` – Taylor order
* `U` – input set
* `k` – window index
* `t` – time

## Hypotheses
* `hΔt` – step length positive
* `hε` – scaled norm small enough for the Taylor order
* `h0` – origin in the input set
* `ht0` – time nonnegative
* `htk` – time within the window end

## Conclusion
* the input reach at the time lies in the accumulated particular solution

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.
* [2] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control, 2007.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The recursion encloses the propagation of the one-step set, window by
window: `plus` absorbs one propagated copy at a time, as the operation builds it. -/
private theorem LinearSys.aux_propagate_subset_particularSolution (sys : LinearSys 𝕋 n) (Δt : ℝ)
    (η : ℕ) (U : S n) : ∀ k : ℕ,
    sys.propagateInputSolution Δt (construct (sys.inputSolution Δt η U)) (k + 1)
      ⊆ construct (sys.particularSolution Δt η U k)
  | 0 => by
    -- `{0} + e^{A·0} P^R(Δt)` is `P^R(Δt)` itself
    intro y hy
    simpa [LinearSys.propagateInputSolution, LinearSys.particularSolution] using hy
  | k + 1 => by
    -- one more window: the accumulated set, plus the one-step set carried by `e^{A t_{k+1}}`
    rw [LinearSys.propagateInputSolution]
    refine subset_trans (Set.add_subset_add
      (sys.aux_propagate_subset_particularSolution Δt η U k) ?_) (Plus.plus_outer _ _)
    rintro _ ⟨y, hy, rfl⟩
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hy))


-- =======================================  MAIN THEOREM  ======================================= --

/-- Everything an admissible input contributes by any `t ≤ t_{k+1}` lies in
`P^R(t_{k+1})` as `particularSolution` computes it. -/
theorem LinearSys.inputReach_subset_particularSolution
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]
    (sys : LinearSys 𝕋 n) {Δt : ℝ} (hΔt : 0 < Δt) {η : ℕ}
    (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) {U : S n}
    (h0 : (0 : Vec ℝ n) ∈ construct U) (k : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (htk : t ≤ ((k + 1 : ℕ) : ℝ) * Δt) : -- --- CONCL ---
    sys.inputReach U t ⊆ construct (sys.particularSolution Δt η U k) := by -- --- PROOF ---
  have hbdd := CompactSet.isBounded_construct U
  -- [2, Prop. 2]: one step of the input, inside `inputSolution`
  have hΔ : sys.inputReach U Δt ⊆ construct (sys.inputSolution Δt η U) :=
    sys.inputReach_subset_inputSolution hΔt η hε (ConvexSet.convex_construct U)
      (CompactSet.isClosed_construct U) hbdd (ConvexSet.convex_construct _)
      (CompactSet.isClosed_construct _) (CompactSet.isBounded_construct _)
  calc sys.inputReach U t
      -- [1, Prop. 4]: `0 ∈ U`, so the window's right end bounds every earlier time
      ⊆ sys.inputReach U (((k + 1 : ℕ) : ℝ) * Δt) := sys.inputReach_mono hbdd h0 ht0 htk
    -- [1, Prop. 4]: exactly the one-step set, propagated `k + 1` times
    _ = sys.propagateInputSolution Δt (sys.inputReach U Δt) (k + 1) :=
      (sys.propagateInputSolution_inputReach hΔt.le hbdd ⟨0, h0⟩ (k + 1)).symm
    _ ⊆ sys.propagateInputSolution Δt (construct (sys.inputSolution Δt η U)) (k + 1) :=
      sys.propagateInputSolution_mono Δt hΔ (k + 1)
    _ ⊆ construct (sys.particularSolution Δt η U k) :=
      sys.aux_propagate_subset_particularSolution Δt η U k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
