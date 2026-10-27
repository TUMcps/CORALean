module

public import CORALean.ContDynamics.NonlinearSys.Theorems.MinkowskiDiffAddSubsetReachSetExact
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffAddAssoc

@[expose] public section

/-!
# A time-interval inner set from the chords instead of the hull

[1, Prop. 2] with the repair of its proof: (23)'s `conv(X₀, R_aff(Δt))` replaced by the chords
`a = x₀ + (t/Δt)(e^{AΔt}x₀ + R_con - x₀)`, the points the printed proof writes every state by, and
the differences `⊖ C ⊖ R̂_err` taken at each `t`, on the slice `{a | x₀ ∈ X₀}`. The union over
`t ∈ [0, Δt]` of `((slice ⊖ C) ⊖ R̂_err) + 2c` lies in `R(τ₀)`, `E = C ⊕ R̂_err` (22) centrally
symmetric about `c`; each slice is `[1, Prop. 1]` at time `t`, with the matrix
`(1 - t/Δt)I + (t/Δt)e^{AΔt}`, which must be invertible. That every solution stays within `E` of
its chord is a hypothesis, as (21) is for `Prop. 1`. `⊖` of the whole chord union is not sound,
even for a convex `X₀` (`NonlinearSys.minkowskiDiff_iUnion_chord_convex_counterexample`).

## Inputs
* `sys` – system
* `R₀` – initial set
* `U` – input set
* `Δt` – step size
* `M` – transition matrix
* `v` – particular solution
* `C` – curvature error set
* `Rerr` – abstraction error set
* `c` – center of symmetry
* `u₀` – constant input
* `Ω` – Lipschitz region
* `K` – Lipschitz constant

## Hypotheses
* `hM` – interpolated matrix invertible at every time
* `hE` – error set compact
* `hEc` – error set convex
* `hEne` – error set nonempty
* `hEs` – error set symmetric about center
* `hu₀` – input in input set
* `hLip` – field Lipschitz on region
* `hex` – solutions exist from every start
* `herr` – solutions lie within the error set of their chord

## Conclusion
* the union of the shifted slice differences lies in the exact time-interval reachable set

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Matrix Pointwise

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2], repaired: `⋃_{t ∈ [0, Δt]} ((chords(t) ⊖ C) ⊖ R̂_err) + 2c ⊆ R(τ₀)`, given that
every solution stays within `E = C ⊕ R̂_err` of its chord. -/
theorem NonlinearSys.minkowskiDiff_chord_subset_reachSetExact (sys : NonlinearSys n m)
    (R₀ : S n) (U : S m) {Δt : ℝ} (M : Mat ℝ n n)
    (hM : ∀ t ∈ Set.Icc 0 Δt, IsUnit ((1 - t / Δt) • (1 : Mat ℝ n n) + (t / Δt) • M).det)
    (v : Vec ℝ n) (C Rerr : Set (Vec ℝ n)) (hE : IsCompact (C + Rerr))
    (hEc : Convex ℝ (C + Rerr)) (hEne : (C + Rerr).Nonempty) {c : Vec ℝ n}
    (hEs : ∀ e ∈ C + Rerr, (2 : ℝ) • c - e ∈ C + Rerr) {u₀ : Vec ℝ m} (hu₀ : u₀ ∈ construct U)
    {Ω : Set (Vec ℝ n)} {K : NNReal} (hLip : LipschitzOnWith K (fun x => sys.f x u₀) Ω)
    (hex : ∀ x₀ ∈ construct R₀, ∃ x : ℝ → Vec ℝ n, x 0 = x₀ ∧ ∀ t ∈ Set.Icc 0 Δt,
      x t ∈ Ω ∧ HasDerivWithinAt x (sys.f (x t) u₀) (Set.Icc 0 Δt) t)
    (herr : ∀ t ∈ Set.Icc 0 Δt, ∀ x₀ ∈ construct R₀, ∀ x : ℝ → Vec ℝ n, x 0 = x₀ →
      (∀ s ∈ Set.Icc 0 t, HasDerivWithinAt x (sys.f (x s) u₀) (Set.Icc 0 t) s) →
      x t - (x₀ + (t / Δt) • (M *ᵥ x₀ + v - x₀)) ∈ C + Rerr) : -- --- CONCL ---
    ⋃ t ∈ Set.Icc 0 Δt, (fun s => s + (2 : ℝ) • c) '' minkowskiDiff
        (minkowskiDiff ((fun x₀ => x₀ + (t / Δt) • (M *ᵥ x₀ + v - x₀)) '' construct R₀) C) Rerr
      ⊆ ⋃ t ∈ Set.Icc 0 Δt, sys.reachSetExact (Set.Icc 0 t) R₀ U t := by -- --- PROOF ---
  refine Set.iUnion₂_subset fun t ht => ?_
  -- the chord point is the affine map `Mₜ x₀ + vₜ` of `Prop. 1` at time `t`
  set Mt : Mat ℝ n n := (1 - t / Δt) • (1 : Mat ℝ n n) + (t / Δt) • M
  have hchord : (fun x₀ => x₀ + (t / Δt) • (M *ᵥ x₀ + v - x₀)) =
      fun x₀ => Mt *ᵥ x₀ + (t / Δt) • v := funext fun x₀ => by
    simp only [Mt, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    module
  rw [← minkowskiDiff_add_assoc, hchord]
  -- `Prop. 1` at time `t`, the solutions on `[0, Δt]` restricted to `[0, t]`
  refine subset_trans ?_ (Set.subset_biUnion_of_mem (u := fun t =>
    sys.reachSetExact (Set.Icc 0 t) R₀ U t) ht)
  refine NonlinearSys.minkowskiDiff_add_subset_reachSetExact sys R₀ U ht.1 Mt (hM t ht) _ hE hEc
    hEne hEs hu₀ hLip (fun x₀ hx₀ => ?_) (fun x₀ hx₀ x hx0 hder => ?_)
  · obtain ⟨x, hx0, hx⟩ := hex x₀ hx₀
    exact ⟨x, hx0, fun s hs => ⟨(hx s ⟨hs.1, hs.2.trans ht.2⟩).1,
      ((hx s ⟨hs.1, hs.2.trans ht.2⟩).2.mono (Set.Icc_subset_Icc_right ht.2))⟩⟩
  · have h := herr t ht x₀ hx₀ x hx0 hder
    rwa [congrFun hchord x₀] at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
