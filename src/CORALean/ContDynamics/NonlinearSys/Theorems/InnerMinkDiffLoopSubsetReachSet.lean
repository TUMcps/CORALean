module

public import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiffLoop
public import CORALean.ContDynamics.NonlinearSys.Theorems.InnerMinkDiffStepSubsetReachSet
public import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetSubsetReachSetAdd

@[expose] public section

/-!
# The time-point sets of the inner algorithm are inner approximations

[1, Alg. 1]'s time-point sets: after `k` steps from `X₀`, `R̂(t_k) ⊆ R(t_k)`, `t_k = kΔt`, the
states some run from `X₀` reaches at `t_k`. The induction is over the steps: `R̂(t_k)` holds
only reachable states, every state of `R̂(t_{k+1})` is reached from one of them in `Δt`
(`innerMinkDiffStep_subset_reachSet`, line 15 by `Prop. 1`), and a run to a reachable state
continued by a run from it is a run from `X₀` (`reachSet_subset_reachSet_add`); `R̂(t₀) = X₀`
is reached at `0` by the run that starts there. `innerMinkDiffLoop_add` makes this a statement
about every time-point set a run of `ω ≥ k` steps computes.

What each step needs is `Prop. 1`'s hypotheses (`InnerMinkDiffCert`), asked for every step
started from reachable states, which is every step: solutions that exist, (21), which the
remainder loop certifies (`InnerMinkDiffCert.of_abstractionError`), and `R̂_err(L̂)` convex,
compact, nonempty and symmetric about line 14's `c = cen(C) + cen(R̂_err(L̂))`. A bounded set
has one centre of symmetry, so with `cen(R̂_err(L̂))` that centre this needs `cen(C) = 0`;
`Prop. 1` shifts by `2 cen(R̂_err)` alone.

Runs are under the constant input `u₀` of the autonomous (4) of [1], so under any `U ∋ u₀`.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Set

variable {n m : ℕ} {𝓛 : Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1]: every time-point set `R̂(t_k)` lies in the reachable set `R(t_k)`, given
`Prop. 1`'s hypotheses at every step. -/
theorem NonlinearSys.innerMinkDiffLoop_subset_reachSet (ops : NonlinearSys.InnerMinkDiffOps n 𝓛)
    (sys : NonlinearSys n m) (u₀ : Vec ℝ m) (U : Set (Vec ℝ m)) (hu₀ : u₀ ∈ U) {Δt : ℝ}
    (hΔt : 0 ≤ Δt) (μ : ℝ) (fuel : ℕ) (X₀ : Set (Vec ℝ n))
    (hcert : ∀ (T : ℝ) (X : Set (Vec ℝ n)) (st : NonlinearSys.InnerMinkDiffState n 𝓛),
      X ⊆ sys.reachSet (S := fun k => Set (Vec ℝ k)) (Icc 0 T) X₀ {u₀} T →
      NonlinearSys.innerMinkDiffStep ops (fun x => sys.f x u₀) Δt μ fuel X = some st →
      NonlinearSys.InnerMinkDiffCert sys u₀ Δt X st)
    {k : ℕ} {Rtk Rτ : Set (Vec ℝ n)}
    (h : NonlinearSys.innerMinkDiffLoop ops (fun x => sys.f x u₀) Δt μ fuel k X₀ ∅ =
      some (Rtk, Rτ)) :
    Rtk ⊆ sys.reachSet (S := fun k => Set (Vec ℝ k)) (Icc 0 (k * Δt)) X₀ U
      (k * Δt) := by -- --- PROOF ---
  -- the induction over the steps, from any time `T` whose reachable set holds the start
  have step : ∀ (j : ℕ) (T : ℝ) (X Y X' Y' : Set (Vec ℝ n)), 0 ≤ T →
      X ⊆ sys.reachSet (S := fun k => Set (Vec ℝ k)) (Icc 0 T) X₀ {u₀} T →
      NonlinearSys.innerMinkDiffLoop ops (fun x => sys.f x u₀) Δt μ fuel j X Y = some (X', Y') →
      X' ⊆ sys.reachSet (S := fun k => Set (Vec ℝ k)) (Icc 0 (T + j * Δt)) X₀ {u₀}
        (T + j * Δt) := by
    intro j
    induction j with
    | zero =>
      intro T X Y X' Y' _ hX hl
      simp only [NonlinearSys.innerMinkDiffLoop, Option.some.injEq, Prod.mk.injEq] at hl
      rw [← hl.1, Nat.cast_zero, zero_mul, add_zero]
      exact hX
    | succ j ih =>
      intro T X Y X' Y' hT hX hl
      obtain ⟨st, hst, hl⟩ := Option.bind_eq_some_iff.mp hl
      have h1 := (NonlinearSys.innerMinkDiffStep_subset_reachSet ops sys u₀ hΔt μ fuel hst
        (hcert T X st hX hst)).trans (sys.reachSet_subset_reachSet_add X₀ X u₀ hT hΔt hX)
      have h2 := ih (T + Δt) _ _ X' Y' (by positivity) h1 hl
      rwa [show T + Δt + (j : ℝ) * Δt = T + ((j + 1 : ℕ) : ℝ) * Δt by push_cast; ring] at h2
  -- `R̂(t₀) = X₀` is reached at `0`: on `{0}` any derivative is one
  have base : X₀ ⊆ sys.reachSet (S := fun k => Set (Vec ℝ k)) (Icc 0 0) X₀ {u₀} 0 := by
    intro y hy
    refine ⟨fun _ => y, fun _ => u₀, ⟨hy, fun _ _ => rfl, fun t ht => ?_⟩, rfl⟩
    rw [Icc_self] at ht ⊢
    rw [mem_singleton_iff.mp ht, hasDerivWithinAt_iff_tendsto_slope, sdiff_self,
      nhdsWithin_empty]
    exact Filter.tendsto_bot
  have hk := step k 0 X₀ ∅ Rtk Rτ le_rfl base h
  rw [zero_add] at hk
  -- runs under `u₀` are runs with inputs in `U`
  rintro y hy
  obtain ⟨x, u, traj, hx⟩ := hk hy
  refine ⟨x, u, ⟨traj.init, fun t ht => ?_, traj.flow⟩, hx⟩
  have hu : u t = u₀ := traj.input t ht
  show u t ∈ U
  rw [hu]
  exact hu₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
