module

public import CORALean.ContDynamics.LinearSys.Operations.VerifySearchLoop
public import CORALean.ContDynamics.LinearSys.Theorems.ConvexHullSupportCounterexampleSubsetReachSet
public import CORALean.ContDynamics.LinearSys.Theorems.ReachSetConvex
public import CORALean.ContDynamics.LinearSys.Theorems.SupportUpperOuter
public import CORALean.ContSet.ContSet.Definitions.CompactSet
public import CORALean.ContSet.ContSet.Definitions.ConvexSet

@[expose] public section

/-!
# The two exits of [1, Alg. 3 (search)] are sound, whatever the search does

`safe` (line 5) says `R(t)` and `L` are disjoint, and `violated` (line 13) that they meet,
whichever directions the search takes, whichever facets it picks and however often it halves
`Δt`: the exits read only the bounds of `Alg. 1`, which are sound at every `Δt = t/k` the loop
visits, and a point of `P̌`, always a difference of a state of `R(t)` and a point of `L`. The loop
carries three invariants: `0 < Δt`, `kΔt = t` with `Δt` small enough for `supportUpper_outer`, and
every vertex of `P̌` in `R(t) - L`; `R(t) - L` is convex, so `0 ∈ conv(P̌)` puts `0` in it.
The oracles are held to what the exits read: `ρL` and `ρ` bound, `ν₀`, `νU` and `νL` are points of
their sets, and `inHull V = true` means the origin is in the hull of `V`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]
variable [∀ n, Recenter (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 3 (search)]: from loop variables with `0 < Δt`, `kΔt = t`, a small enough `Δt` and
every vertex of `P̌` in `R(t) - L`, a `safe` answer means `R(t) ∩ L = ∅` and a `violated` one
means `R(t) ∩ L ≠ ∅`. -/
theorem LinearSys.verifySearchLoop_sound
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]
    (sys : LinearSys 𝕋 n) (X₀ U : S n) (hX₀ : Convex ℝ (construct X₀))
    (hUconv : Convex ℝ (construct U)) {t : ℝ} {m : ℕ}
    {ρ : S n → (Vec ℝ n →ₗ[ℝ] ℝ) → ℝ}
    (hρ : ∀ X : S n, ∀ x ∈ construct X, ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, d x ≤ ρ X d)
    {ν₀ νU νL : (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n} (hν₀ : ∀ d, ν₀ d ∈ construct X₀)
    (hνU : ∀ d, νU d ∈ construct U) {L : Set (Vec ℝ n)} (hL : Convex ℝ L)
    (hνL : ∀ d, νL d ∈ L) {ρL : (Vec ℝ n →ₗ[ℝ] ℝ) → ℝ} (hρL : ∀ d, ∀ y ∈ L, d y ≤ ρL d)
    {νhat : ℝ → (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n} {inHull : List (Vec ℝ n) → Bool}
    (hhull : ∀ V, inHull V = true → (0 : Vec ℝ n) ∈ convexHull ℝ {v | v ∈ V})
    (closestFacet : List (Vec ℝ n) → (Vec ℝ n →ₗ[ℝ] ℝ) × List ℕ)
    (gramSchmidt : List (Vec ℝ n) → (Vec ℝ n →ₗ[ℝ] ℝ)) (ℓ₁ : Vec ℝ n →ₗ[ℝ] ℝ) (fuel : ℕ)
    (s : LinearSys.VerifySearchState n) (hΔt : 0 < s.Δt) (hk : (s.k : ℝ) * s.Δt = t)
    (hε : ‖s.Δt • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    (hP : ∀ v ∈ s.Pcheck, v ∈ sys.reachSet (Set.Icc 0 t) X₀ U t - L) : -- --- STMT ---
    (sys.verifySearchLoop X₀ U (m + 2) ρ ν₀ νU νL νhat ρL inHull closestFacet gramSchmidt ℓ₁ fuel s
        = .safe → Disjoint (sys.reachSet (Set.Icc 0 t) X₀ U t) L) ∧
    (sys.verifySearchLoop X₀ U (m + 2) ρ ν₀ νU νL νhat ρL inHull closestFacet gramSchmidt ℓ₁ fuel s
        = .violated → ¬ Disjoint (sys.reachSet (Set.Icc 0 t) X₀ U t) L) := by -- --- PROOF ---
  induction fuel generalizing s with
  | zero => exact ⟨fun h => by simp [LinearSys.verifySearchLoop] at h,
      fun h => by simp [LinearSys.verifySearchLoop] at h⟩
  | succ fuel ih =>
    -- `R(t)` is convex, so is `R(t) - L`, and the bounds of `Alg. 1` hold along `ℓ_i`
    have ht0 : 0 ≤ t := hk ▸ mul_nonneg s.k.cast_nonneg hΔt.le
    have hU : Bornology.IsBounded (construct U) := CompactSet.isBounded_construct U
    have hRL : Convex ℝ (sys.reachSet (Set.Icc 0 t) X₀ U t - L) :=
      (sys.reachSet_convex ht0 hX₀ hUconv hU).sub hL
    have hup := (sys.supportUpper_outer hΔt hε X₀ U hρ s.ℓ s.k).1
    rw [hk] at hup
    -- the support vector of the inner approximation is a state of `R(t)`
    have hv := sys.convexHull_supportCounterexample_subset_reachSet X₀ U hX₀ hUconv hU hΔt hν₀
      hνU (fun _ : Unit => s.ℓ) s.k
    rw [hk] at hv
    have hvc := Set.sub_mem_sub (hv (subset_convexHull ℝ _ ⟨(), rfl⟩)) (hνL (-s.ℓ))
    -- the new vertex joins `P̌` and the hull of the longer list is still inside `R(t) - L`
    have hvert : ∀ v ∈ s.Pcheck ++ [sys.heldSim s.Δt
        (sys.supportCounterexample s.Δt ν₀ νU s.ℓ s.k).1
        (sys.supportCounterexample s.Δt ν₀ νU s.ℓ s.k).2 s.k - νL (-s.ℓ)],
        v ∈ sys.reachSet (Set.Icc 0 t) X₀ U t - L := by
      intro v hv'
      rcases List.mem_append.mp hv' with h | h
      · exact hP v h
      · rw [List.mem_singleton.mp h]
        exact hvc
    simp only [LinearSys.verifySearchLoop]
    split
    next h1 =>
      -- line 4-5: `ℓ_i` separates, so the two sets are disjoint
      refine ⟨fun _ => Set.disjoint_left.mpr fun x hx hxL => ?_,
        fun h => VerifyAnswer.noConfusion h⟩
      have h2 := hρL (-s.ℓ) x hxL
      rw [LinearMap.neg_apply] at h2
      linarith [hup x hx]
    next h1 =>
      split
      next h2 =>
        -- line 12-13: the origin is in the hull of differences, so the sets meet
        refine ⟨fun h => VerifyAnswer.noConfusion h, fun _ => ?_⟩
        have h0 := convexHull_min (fun v hv' => hvert v (by simpa using hv')) hRL (hhull _ h2)
        obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_sub.mp h0
        exact Set.not_disjoint_iff.mpr ⟨x, hx, (sub_eq_zero.mp hxy) ▸ hy⟩
      next h2 =>
        split
        next h3 =>
          -- line 15-16: `Δt` halved, so `k` doubled, and the lists emptied
          refine ih _ (half_pos hΔt) ?_ ?_ (fun v hv' => by simp at hv')
          · push_cast
            linarith
          · calc ‖(s.Δt / 2) • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2)
                ≤ ‖s.Δt • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) := by
                  refine div_le_div_of_nonneg_right ?_ (by positivity)
                  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hΔt,
                    abs_of_pos (half_pos hΔt)]
                  exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
              _ < 1 := hε
        next h3 =>
          split
          next h4 =>
            -- line 19-21: the facet closest to the origin
            refine ih _ hΔt hk hε fun v hv' => hvert v ?_
            obtain ⟨j, -, hj⟩ := List.mem_filterMap.mp hv'
            exact List.mem_of_getElem? hj
          next h4 =>
            -- line 23: a direction orthogonal to the vertices
            exact ih _ hΔt hk hε hvert

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
