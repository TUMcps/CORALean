module

public import CORALean.ContDynamics.NonlinearSys.Theorems.LinReachInnerSubsetReachSet
public import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetSubsetReachSetAdd

@[expose] public section

/-!
# CORA's inner linearized step: the time-interval set is inside the reachable set

The time-interval set `Rti` CORALean's `linReachInner` returns in place of CORA's [1, Prop. 2]
hull, `Rinit ∪ Rtp`, lies in the time-interval reachable set `R([T, T + Δt]) = ⋃_t R(t)`
[1, Def. 1] when the start set `Rinit` holds only states reached at `T`: `Rinit ⊆ R(T)`, and
`Rtp` is reached at `Δt` from `Rinit` (`linReachInner_subset_reachSet`), so at `T + Δt` from
`X₀` (`reachSet_subset_reachSet_add`). CORA's own `Rti` is not inside it
(`convexHull_timeInterval_convex_counterexample`).

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Set

variable {n m : ℕ} {𝓛 : Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `linReachInner`'s `Rti ⊆ R([T, T + Δt])` from `X = Rinit ⊆ R(T)`, given `Prop. 1`'s
hypotheses. -/
theorem NonlinearSys.linReachInner_Rti_subset_reachSet (ops : NonlinearSys.LinReachInnerOps n 𝓛)
    (sys : NonlinearSys n m) (u₀ : Vec ℝ m) (X₀ : Set (Vec ℝ n)) {T Δt : ℝ} (hT : 0 ≤ T)
    (hΔt : 0 ≤ Δt) (fuel : ℕ) {X : Set (Vec ℝ n)} {e : Vec ℝ n}
    {st : NonlinearSys.LinReachInnerState n 𝓛}
    (hX : X ⊆ sys.reachSet (S := 𝒮) (Icc 0 T) X₀ {u₀} T)
    (h : NonlinearSys.linReachInner ops (fun x => sys.f x u₀) Δt fuel X e = some (some st))
    (cert : NonlinearSys.IsLinReachInnerCert sys u₀ Δt X st) :
    st.Rti ⊆ ⋃ t ∈ Icc T (T + Δt),
      sys.reachSet (S := 𝒮) (Icc 0 t) X₀ {u₀} t := by -- --- PROOF ---
  have hRti : st.Rti = X ∪ st.Rtp := by
    unfold NonlinearSys.linReachInner at h
    dsimp only at h
    split_ifs at h
    · simp at h
    obtain ⟨_, -, hr⟩ := Option.map_eq_some_iff.mp h
    obtain rfl := Option.some.inj hr
    rfl
  rw [hRti]
  refine union_subset ?_ ?_
  · -- `Rinit` at `T`
    exact hX.trans (subset_biUnion_of_mem (u := fun t =>
      sys.reachSet (S := 𝒮) (Icc 0 t) X₀ {u₀} t)
      (⟨le_rfl, by linarith⟩ : T ∈ Icc T (T + Δt)))
  · -- `Rtp` at `T + Δt`
    exact ((NonlinearSys.linReachInner_subset_reachSet ops sys u₀ hΔt fuel h cert).trans
      (sys.reachSet_subset_reachSet_add X₀ X u₀ hT hΔt hX)).trans
      (subset_biUnion_of_mem (u := fun t =>
        sys.reachSet (S := 𝒮) (Icc 0 t) X₀ {u₀} t)
        (⟨by linarith, le_rfl⟩ : T + Δt ∈ Icc T (T + Δt)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
