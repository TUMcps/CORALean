module

public import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiffCorrectedLoop
public import CORALean.ContDynamics.NonlinearSys.Theorems.InnerMinkDiffCorrectedStepSubsetReachSetExact
public import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetExactSubsetReachSetExactAdd

@[expose] public section

/-!
# The sets of the corrected inner algorithm are inner approximations

The corrected [1, Alg. 1] from a convex `X₀`, after `k` steps of size `Δt`: the time-point set
`R̂(t_k)` lies in `R(t_k)`, the time-interval set `R̂(τ_k)` the next step computes from it lies in
the states reached at some `t ∈ τ_k = [t_k, t_{k+1}]`, and the union of the time-interval sets
so far in those reached over `[0, t_k]`. By induction over the steps, each one
`innerMinkDiffCorrectedStep_subset_reachSetExact`, which also hands on the convexity of
`R̂(t_{k+1})` the next hull erosion needs; a run continued by a run is a run from `X₀`. The
hypotheses are on the run: every step it takes, from the `R̂(t_j)` it computed, has its
certificate (`IsInnerMinkDiffCorrectedCert`). Runs are under the constant input `u₀` of (4).

## Inputs
* `ops` – set operations
* `zono` – zonotope of a set's center and generators
* `sys` – system
* `u₀` – constant input
* `U` – input set
* `Δt` – step size
* `μ` – enlargement factor
* `fuel` – bound per remainder loop
* `X₀` – initial set
* `k` – number of steps

## Hypotheses
* `hu₀` – input in input set
* `hΔt` – step size positive
* `hX₀` – initial set convex
* `hcert` – every step of the run has its certificate

## Conclusion
* the time-point set, the next time-interval set and the union so far lie in the exact
  reachable sets

## References

* [1] [M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
      2024.](../../../../../references/2024/wetzlinger-lcss-inner-minkowski-difference.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Set MeasureTheory

variable {n m : ℕ} {𝓛 : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `k + 1` steps of the corrected loop are `k` steps, then one more. -/
private theorem NonlinearSys.aux_innerMinkDiffCorrectedLoop_succ
    (ops : NonlinearSys.InnerMinkDiffOps n 𝓛) (zono : Set (Vec ℝ n) → Real.Zonotope (Vec ℝ n))
    (f : Vec ℝ n → Vec ℝ n) (Δt μ : ℝ) (fuel k : ℕ) (Rtk Rτ : Set (Vec ℝ n)) : -- --- CONCL ---
    NonlinearSys.innerMinkDiffCorrectedLoop ops zono f Δt μ fuel (k + 1) Rtk Rτ =
      (NonlinearSys.innerMinkDiffCorrectedLoop ops zono f Δt μ fuel k Rtk Rτ).bind fun p =>
        (NonlinearSys.innerMinkDiffCorrectedStep ops zono f Δt μ fuel p.1).bind fun st =>
          some (st.Rtk1, p.2 ∪ st.Rtauk) := by -- --- PROOF ---
  induction k generalizing Rtk Rτ with
  | zero =>
    simp only [NonlinearSys.innerMinkDiffCorrectedLoop, Option.bind_some]
  | succ k ih =>
    rw [NonlinearSys.innerMinkDiffCorrectedLoop]
    conv_rhs => rw [NonlinearSys.innerMinkDiffCorrectedLoop]
    simp only [ih, Option.bind_assoc]

/-- Runs under `u₀` are runs with inputs in `U ∋ u₀`. -/
private theorem NonlinearSys.aux_reachSetExact_singleton_subset (sys : NonlinearSys n m)
    (X₀ : Set (Vec ℝ n)) {u₀ : Vec ℝ m} {U : Set (Vec ℝ m)} (hu₀ : u₀ ∈ U)
    (t : ℝ) : -- --- CONCL ---
    sys.reachSetExact (S := 𝒮) (Icc 0 t) X₀ {u₀} t ⊆
      sys.reachSetExact (S := 𝒮) (Icc 0 t) X₀ U t := by -- --- PROOF ---
  rintro y ⟨x, u, traj, hx⟩
  refine ⟨x, u, ⟨traj.init, fun s hs => ?_, traj.meas, traj.integrable, traj.cont, traj.flow,
      traj.output⟩, hx⟩
  have hu : u s = u₀ := traj.input s hs
  show u s ∈ U
  rw [hu]
  exact hu₀


-- =======================================  MAIN THEOREM  ======================================= --

/-- The corrected [1, Alg. 1] from a convex `X₀`: `R̂(t_k) ⊆ R(t_k)`, `R̂(τ_k) ⊆ R(τ_k)` and the
union of the time-interval sets so far in `R([0, t_k])`, given each step's certificate. -/
theorem NonlinearSys.innerMinkDiffCorrectedLoop_subset_reachSetExact
    (ops : NonlinearSys.InnerMinkDiffOps n 𝓛) (zono : Set (Vec ℝ n) → Real.Zonotope (Vec ℝ n))
    (sys : NonlinearSys n m) (u₀ : Vec ℝ m) (U : Set (Vec ℝ m)) (hu₀ : u₀ ∈ U) {Δt : ℝ}
    (hΔt : 0 < Δt) (μ : ℝ) (fuel : ℕ) (X₀ : Set (Vec ℝ n)) (hX₀ : Convex ℝ X₀) {k : ℕ}
    (hcert : ∀ j < k, ∀ (X Y : Set (Vec ℝ n)) (st : NonlinearSys.InnerMinkDiffState n 𝓛),
      NonlinearSys.innerMinkDiffCorrectedLoop ops zono (fun x => sys.f x u₀) Δt μ fuel j X₀ ∅ =
        some (X, Y) →
      NonlinearSys.innerMinkDiffCorrectedStep ops zono (fun x => sys.f x u₀) Δt μ fuel X =
        some st →
      NonlinearSys.IsInnerMinkDiffCorrectedCert sys u₀ Δt ops zono X st) : -- --- CONCL ---
    ∀ p ∈ NonlinearSys.innerMinkDiffCorrectedLoop ops zono (fun x => sys.f x u₀) Δt μ fuel k X₀ ∅,
      p.1 ⊆ sys.reachSetExact (S := 𝒮) (Icc 0 (k * Δt)) X₀ U (k * Δt) ∧
      (∀ st ∈ NonlinearSys.innerMinkDiffCorrectedStep ops zono (fun x => sys.f x u₀) Δt μ fuel p.1,
        NonlinearSys.IsInnerMinkDiffCorrectedCert sys u₀ Δt ops zono p.1 st →
        st.Rtauk ⊆ ⋃ t ∈ Icc (k * Δt) ((k + 1) * Δt),
          sys.reachSetExact (S := 𝒮) (Icc 0 t) X₀ U t) ∧
      p.2 ⊆ ⋃ t ∈ Icc 0 (k * Δt),
        sys.reachSetExact (S := 𝒮) (Icc 0 t) X₀ U t := by -- --- PROOF ---
  rintro ⟨Rtk, Rτ⟩ (h : _ = some _)
  -- the invariant under `u₀`: both inclusions and the convexity of `R̂(t_j)`
  have inv : ∀ j ≤ k, ∀ X Y : Set (Vec ℝ n),
      NonlinearSys.innerMinkDiffCorrectedLoop ops zono (fun x => sys.f x u₀) Δt μ fuel j X₀ ∅ =
        some (X, Y) →
      X ⊆ sys.reachSetExact (S := 𝒮) (Icc 0 (j * Δt)) X₀ {u₀} (j * Δt) ∧ Convex ℝ X ∧
      Y ⊆ ⋃ t ∈ Icc 0 (j * Δt), sys.reachSetExact (S := 𝒮) (Icc 0 t) X₀ {u₀} t := by
    intro j
    induction j with
    | zero =>
      intro _ X Y hl
      simp only [NonlinearSys.innerMinkDiffCorrectedLoop, Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      rw [Nat.cast_zero, zero_mul]
      refine ⟨fun y hy => ?_, hX₀, empty_subset _⟩
      -- `R̂(t₀) = X₀` is reached at `0`: on `{0}` the constant is a run
      refine ⟨fun _ => y, fun _ => u₀, ⟨hy, fun _ _ => rfl, aestronglyMeasurable_const,
        fun _ _ => intervalIntegrable_const, continuousOn_const, fun t ht => ?_,
        fun _ _ => rfl⟩, rfl⟩
      rw [Icc_self, mem_singleton_iff] at ht
      subst ht
      simp
    | succ j ih =>
      intro hj X' Y' hl
      rw [aux_innerMinkDiffCorrectedLoop_succ] at hl
      obtain ⟨⟨X, Y⟩, hp, hl⟩ := Option.bind_eq_some_iff.mp hl
      obtain ⟨st, hst, hl⟩ := Option.bind_eq_some_iff.mp hl
      simp only [Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      -- the step from `R̂(t_j)`, with the invariant there
      obtain ⟨hX, hXc, hY⟩ := ih (by omega) X Y hp
      have hT : 0 ≤ (j : ℝ) * Δt := by positivity
      obtain ⟨h1, h2, h3⟩ := NonlinearSys.innerMinkDiffCorrectedStep_subset_reachSetExact ops zono
        sys u₀ hΔt μ fuel hXc st hst (hcert j (by omega) X Y st hp hst)
      have ht : ((j + 1 : ℕ) : ℝ) * Δt = j * Δt + Δt := by push_cast; ring
      rw [ht]
      refine ⟨h1.trans (sys.reachSetExact_subset_reachSetExact_add X₀ X u₀ hT hΔt.le hX), h3,
        union_subset (hY.trans (biUnion_mono (Icc_subset_Icc_right (by linarith)) fun _ _ =>
          subset_rfl)) (h2.trans (iUnion₂_subset fun t ht' => ?_))⟩
      -- a state reached from `R̂(t_j)` at `t ∈ [0, Δt]` is reached from `X₀` at `t_j + t`
      exact (sys.reachSetExact_subset_reachSetExact_add X₀ X u₀ hT ht'.1 hX).trans
        (subset_iUnion₂_of_subset (j * Δt + t) ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
          subset_rfl)
  obtain ⟨hX, hXc, hY⟩ := inv k le_rfl Rtk Rτ h
  refine ⟨hX.trans (aux_reachSetExact_singleton_subset sys X₀ hu₀ _),
    fun st (hst : _ = some _) cert => ?_,
    hY.trans (biUnion_mono subset_rfl fun t _ => aux_reachSetExact_singleton_subset sys X₀ hu₀ t)⟩
  -- the step from `R̂(t_k)`: `[0, Δt]` from `R̂(t_k)` is `τ_k` from `X₀`
  have h2 := (NonlinearSys.innerMinkDiffCorrectedStep_subset_reachSetExact ops zono sys u₀ hΔt μ
    fuel hXc st hst cert).2.1
  have hT : 0 ≤ (k : ℝ) * Δt := by positivity
  refine h2.trans (iUnion₂_subset fun t ht => ?_)
  exact ((sys.reachSetExact_subset_reachSetExact_add X₀ Rtk u₀ hT ht.1 hX).trans
    (aux_reachSetExact_singleton_subset sys X₀ hu₀ _)).trans
    (subset_iUnion₂_of_subset (k * Δt + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩ subset_rfl)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
