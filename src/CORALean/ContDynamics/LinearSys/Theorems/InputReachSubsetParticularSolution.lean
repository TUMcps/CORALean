import CORALean.ContDynamics.LinearSys.Operations.ParticularSolution
import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution
import CORALean.ContDynamics.LinearSys.Theorems.PropagateInputReach
import CORALean.ContDynamics.LinearSys.Theorems.PropagateInputSolutionMono
import CORALean.ContSet.ContSet.Definitions.CompactSet
import CORALean.ContSet.ContSet.Definitions.ConvexSet
import CORALean.ContSet.ContSet.Theorems.IsBoundedConstruct
import CORALean.ContSet.ContSet.Theorems.IsClosedConstruct

/-!
# `particularSolution` holds everything the input contributes by a window's end

Four steps, each proved on its own already. With `0 ∈ U`, the input reach set
grows with time [1, Prop. 3.3], so every `t ≤ t_{k+1}` is bounded by
`P^R(t_{k+1})`; that set is exactly the one-step set propagated `k + 1` times
[1, Prop. 3.2]; propagation preserves enclosure, and [1, Thm. 3.1] encloses the
one step in `inputSolution`; and the recursion `particularSolution` computes
encloses that propagation, one `plus` and one `mtimes` per window.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
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
theorem LinearSys.aux_propagate_subset_particularSolution (sys : LinearSys 𝕋 n) (Δt : ℝ)
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
    (htk : t ≤ ((k + 1 : ℕ) : ℝ) * Δt) :
    sys.inputReach U t ⊆ construct (sys.particularSolution Δt η U k) := by -- --- PROOF ---
  have hbdd := CompactSet.isBounded_construct U
  -- [1, Thm. 3.1]: one step of the input, inside `inputSolution`
  have hΔ : sys.inputReach U Δt ⊆ construct (sys.inputSolution Δt η U) :=
    sys.inputReach_subset_inputSolution hΔt η hε (ConvexSet.convex_construct U)
      (CompactSet.isClosed_construct U) hbdd (ConvexSet.convex_construct _)
      (CompactSet.isClosed_construct _) (CompactSet.isBounded_construct _)
  calc sys.inputReach U t
      -- [1, Prop. 3.3]: `0 ∈ U`, so the window's right end bounds every earlier time
      ⊆ sys.inputReach U (((k + 1 : ℕ) : ℝ) * Δt) := sys.inputReach_mono hbdd h0 ht0 htk
    -- [1, Prop. 3.2]: exactly the one-step set, propagated `k + 1` times
    _ = sys.propagateInputSolution Δt (sys.inputReach U Δt) (k + 1) :=
      (sys.propagateInputSolution_inputReach hΔt.le hbdd ⟨0, h0⟩ (k + 1)).symm
    _ ⊆ sys.propagateInputSolution Δt (construct (sys.inputSolution Δt η U)) (k + 1) :=
      sys.propagateInputSolution_mono Δt hΔ (k + 1)
    _ ⊆ construct (sys.particularSolution Δt η U k) :=
      sys.aux_propagate_subset_particularSolution Δt η U k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
