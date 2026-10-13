import CORALean.ContDynamics.LinearSys.Theorems.ManualRunTEq
import CORALean.ContDynamics.LinearSys.Theorems.MulVecL
import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.HausdorffDist2ReduceLe
import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import CORALean.Global.EuclideanHausdorffDistAddLe
import CORALean.Global.EuclideanHausdorffDistTriangle

/-!
# [1, Prop. 4]'s eq. (28): the reduction error accumulated over the horizon

Line 10 of `Alg. 1` reduces what it has just accumulated and feeds the result back, so the
reductions do compound: `ε^r_k = ∑_{j<k} Δε^r_j(ρ)`, each summand eq. (29)'s bound at the
zonotope that step actually reduced. This is the distance between `manualRun`'s own
`P̂^U(t_k)` and the same recursion with line 10's `reduce` omitted.

Two facts on top of eq. (29) carry the induction, as the `Prop. 4` finding says they must:
the Hausdorff triangle inequality, and the invariance of `d_H` under a common Minkowski
summand — the latter a corollary of `hausdorffDist₂_add_le` at `d_H(X,X) = 0`, no separate
argument needed. Nothing here is about which generators `reduce` drops.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The unreduced accumulation is a finite Minkowski sum of propagated zonotopes, so it is
compact and nonempty at every step — what the triangle inequality asks of it. -/
theorem aux_isCompact_sum_range_mulVec (Z : Zonotope (Vec ℝ n)) (Φ : ℕ → Mat ℝ n n) (k : ℕ) :
    IsCompact (∑ j ∈ Finset.range k, (fun x => Φ j *ᵥ x) '' Z.construct) ∧
      (∑ j ∈ Finset.range k, (fun x => Φ j *ᵥ x) '' Z.construct).Nonempty := by -- --- PROOF ---
  induction k with
  | zero =>
    rw [Finset.sum_range_zero, ← Set.singleton_zero]
    exact ⟨isCompact_singleton, Set.singleton_nonempty 0⟩
  | succ k ih =>
    rw [Finset.sum_range_succ]
    exact ⟨ih.1.add (Z.isCompact_construct.image (mulVecL (Φ k)).continuous),
      ih.2.add (Set.Nonempty.image _ ⟨Z.c, Zonotope.centre_mem_construct Z⟩)⟩

/-- `d_H` ignores a summand both sides share: `hausdorffDist₂_add_le` at `d_H(X,X) = 0`. -/
theorem aux_hausdorffDist₂_add_right {S T X : Set (Vec ℝ n)} (hS : IsCompact S)
    (hSne : S.Nonempty) (hT : IsCompact T) (hTne : T.Nonempty) (hX : IsCompact X)
    (hXne : X.Nonempty) :
    hausdorffDist₂ (S + X) (T + X) ≤ hausdorffDist₂ S T := by
  have hself : hausdorffDist₂ X X = 0 := Metric.hausdorffDist_self_zero
  have h := hausdorffDist₂_add_le hS hSne hT hTne hX hXne hX hXne
  rw [hself, add_zero] at h
  exact h


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 4], eq. (28): `Alg. 1`'s iteratively reduced `P̂^U(t_k)` is within the summed
per-step reduction errors of the same accumulation with line 10's `reduce` omitted. -/
theorem LinearSys.hausdorffDist₂_manualRun_reduce_le (sys : LinearSys 𝕋 n)
    (X₀ U : Zonotope (Vec ℝ n)) (Δt : ℝ) (η ρ k : ℕ) :
    hausdorffDist₂
        (∑ j ∈ Finset.range k, (fun x => exp (((j : ℝ) * Δt) • toRealMat sys.A) *ᵥ x)
          '' (sys.inputSolution (S := 𝒵) Δt η
              ({ h := U.h, c := 0, G := U.G } : Zonotope (Vec ℝ n))).construct)
        (sys.manualRun X₀ U Δt η ρ k).PU.construct
      ≤ ∑ j ∈ Finset.range k, (Zonotope.plus (sys.manualRun X₀ U Δt η ρ j).PU
          (Zonotope.mtimes (exp (((j : ℝ) * Δt) • toRealMat sys.A))
            (sys.inputSolution (S := 𝒵) Δt η
              ({ h := U.h, c := 0, G := U.G } : Zonotope (Vec ℝ n))))).reduceBoxError
          ρ := by -- --- PROOF ---
  have hsum := aux_isCompact_sum_range_mulVec
    (sys.inputSolution (S := 𝒵) Δt η ({ h := U.h, c := 0, G := U.G } : Zonotope (Vec ℝ n)))
    (fun j => exp (((j : ℝ) * Δt) • toRealMat sys.A))
  induction k with
  | zero =>
    rw [Finset.sum_range_zero, Finset.sum_range_zero]
    have h0 : (sys.manualRun X₀ U Δt η ρ 0).PU.construct = {0} := by
      ext x
      simp only [LinearSys.manualRun, LinearSys.manualInit, Zonotope.mem_ofPoint_iff,
        Set.mem_singleton_iff]
    rw [h0, ← Set.singleton_zero]
    refine hausdorffDist₂_le_of_mem_dist (le_refl 0) (fun x hx => ?_) (fun x hx => ?_) <;>
      exact ⟨x, hx, by rw [sub_self, norm₂_zero]⟩
  -- one more step: the accumulation, then the reduction line 10 applies to it
  | succ k ih =>
    have hstep : (sys.manualRun X₀ U Δt η ρ (k + 1)).PU
        = Zonotope.reduce (Zonotope.plus (sys.manualRun X₀ U Δt η ρ k).PU
            (Zonotope.mtimes (exp (((k : ℝ) * Δt) • toRealMat sys.A))
              (sys.inputSolution (S := 𝒵) Δt η
                ({ h := U.h, c := 0, G := U.G } : Zonotope (Vec ℝ n))))) ρ := by
      simp only [LinearSys.manualRun, LinearSys.manualStep, sys.manualRun_t_eq]
    have hXc : IsCompact ((fun x => exp (((k : ℝ) * Δt) • toRealMat sys.A) *ᵥ x)
        '' (sys.inputSolution (S := 𝒵) Δt η
            ({ h := U.h, c := 0, G := U.G } : Zonotope (Vec ℝ n))).construct) :=
      (Zonotope.isCompact_construct _).image (mulVecL _).continuous
    have hXne : ((fun x => exp (((k : ℝ) * Δt) • toRealMat sys.A) *ᵥ x)
        '' (sys.inputSolution (S := 𝒵) Δt η
            ({ h := U.h, c := 0, G := U.G } : Zonotope (Vec ℝ n))).construct).Nonempty :=
      Set.Nonempty.image _ ⟨_, Zonotope.centre_mem_construct _⟩
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hstep]
    -- through the unreduced sum: the step's own accumulation, then line 10's reduction of it
    refine (hausdorffDist₂_triangle ((hsum k).1.add hXc).isBounded ((hsum k).2.add hXne)
      (Zonotope.isBounded_construct _) ⟨_, Zonotope.centre_mem_construct _⟩).trans
      (add_le_add ?_ (Zonotope.hausdorffDist₂_reduce_le _ ρ))
    rw [← Zonotope.plus_exact, ← Zonotope.mtimes_exact]
    exact (aux_hausdorffDist₂_add_right (hsum k).1 (hsum k).2
      (Zonotope.isCompact_construct _) ⟨_, Zonotope.centre_mem_construct _⟩ hXc hXne).trans ih

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
