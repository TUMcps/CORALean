module

public import CORALean.ContDynamics.LinParamSys.Operations.ParticularSolution
public import CORALean.ContDynamics.LinParamSys.Theorems.ExpMemExpEnclosure
public import CORALean.ContDynamics.LinParamSys.Theorems.InputReachSubsetInputSolution
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.PropagateInputReach
public import CORALean.ContDynamics.LinearSys.Theorems.PropagateInputSolutionMono
public import CORALean.ContSet.ContSet.Definitions.CompactSet
public import CORALean.ContSet.ContSet.Definitions.ConvexSet
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# `particularSolution` holds what the input contributes at one member

`LinearSys.inputReach_subset_particularSolution` at a member `A` of `sys.A`,
the point system `⟨A⟩`'s own `P^R(t)`: with `0 ∈ U` it grows with time
[1, Sec. 3.3], is the one-step set propagated `k + 1` times [1, Alg. 1],
and that one step lies in the box's `inputSolution`. Each propagator
`e^{A t_j}` is a member of `expEnclosure t_j`, which is all the recursion needs.

## Inputs
* `sys` – system
* `Δt` – window length
* `η` – Taylor order
* `A` – system matrix member
* `U` – input set
* `k` – window index
* `t` – time

## Hypotheses
* `hΔt` – window length positive
* `hε` – order admissible
* `hA` – `A` lies in the matrix set
* `h0` – origin lies in the input set
* `ht0` – time nonnegative
* `htk` – time at most the window end

## Conclusion
* everything an admissible input contributes by time `t` lies in the particular solution

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
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

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The recursion encloses the member's propagation of the one-step set, window
by window: `plus` absorbs one propagated copy at a time. -/
theorem LinParamSys.aux_propagate_subset_particularSolution (sys : LinParamSys ℐ n)
    (Δt : ℝ) (η : ℕ) (U : S n) {A : Mat ℝ n n} (hA : A ∈ construct sys.A) :
    ∀ k : ℕ,
    (LinearSys.canonical A : LinearSys ℝ n).propagateInputSolution Δt
        (construct (sys.inputSolution Δt η U)) (k + 1)
      ⊆ construct (sys.particularSolution Δt η U k)
  | 0 => by
    -- `{0} + e^{A·0} P^R(Δt)` is `P^R(Δt)` itself
    intro y hy
    simpa [LinearSys.propagateInputSolution, LinParamSys.particularSolution] using hy
  | k + 1 => by
    -- one more window: the accumulated set, plus the one-step set carried by `e^{A t_{k+1}}`
    rw [LinearSys.propagateInputSolution]
    refine subset_trans (Set.add_subset_add
      (sys.aux_propagate_subset_particularSolution Δt η U hA k) ?_) (Plus.plus_outer _ _)
    rintro _ ⟨y, hy, rfl⟩
    refine Mtimes.mtimes_outer _ _ (Set.mem_biUnion ?_ (Set.mem_image_of_mem _ hy))
    have h := sys.exp_mem_expEnclosure (((k + 1 : ℕ) : ℝ) * Δt) η hA
    simp only [Scalar.toRealMat_real]
    exact h


-- =======================================  MAIN THEOREM  ======================================= --

/-- Everything an admissible input contributes under a member `A` by any
`t ≤ t_{k+1}` lies in `P^R(t_{k+1})` as `particularSolution` computes it. -/
theorem LinParamSys.inputReach_subset_particularSolution
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]
    (sys : LinParamSys ℐ n) {Δt : ℝ} (hΔt : 0 < Δt) {η : ℕ}
    (hε : ‖(Interval.smul Δt sys.A).absMax‖ / ((η : ℝ) + 2) < 1)
    {A : Mat ℝ n n} (hA : A ∈ construct sys.A) {U : S n}
    (h0 : (0 : Vec ℝ n) ∈ construct U) (k : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (htk : t ≤ ((k + 1 : ℕ) : ℝ) * Δt) : -- --- CONCL ---
    (LinearSys.canonical A : LinearSys ℝ n).inputReach U t
      ⊆ construct (sys.particularSolution Δt η U k) := by -- --- PROOF ---
  set L : LinearSys ℝ n := LinearSys.canonical A
  have hbdd := CompactSet.isBounded_construct U
  -- [1, Thm. 1]: one step of the input under `A`, inside the box's `inputSolution`
  have hΔ : L.inputReach U Δt ⊆ construct (sys.inputSolution Δt η U) :=
    sys.inputReach_subset_inputSolution hΔt η hε hA (ConvexSet.convex_construct U)
      (CompactSet.isClosed_construct U) hbdd (ConvexSet.convex_construct _)
      (CompactSet.isClosed_construct _) (CompactSet.isBounded_construct _)
  calc L.inputReach U t
      -- [1, Sec. 3.3]: `0 ∈ U`, so the window's right end bounds every earlier time
      ⊆ L.inputReach U (((k + 1 : ℕ) : ℝ) * Δt) := L.inputReach_mono hbdd h0 ht0 htk
    -- [1, Alg. 1]: exactly the one-step set, propagated `k + 1` times
    _ = L.propagateInputSolution Δt (L.inputReach U Δt) (k + 1) :=
      (L.propagateInputSolution_inputReach hΔt.le hbdd ⟨0, h0⟩ (k + 1)).symm
    _ ⊆ L.propagateInputSolution Δt (construct (sys.inputSolution Δt η U)) (k + 1) :=
      L.propagateInputSolution_mono Δt hΔ (k + 1)
    _ ⊆ construct (sys.particularSolution Δt η U k) :=
      sys.aux_propagate_subset_particularSolution Δt η U hA k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
