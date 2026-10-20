module

public import CORALean.ContDynamics.LinearSys.Theorems.HausdorffDist2ManualRunReduceLe

@[expose] public section

/-!
# [1, Prop. 4]'s eq. (28) at varying step parameters

`HausdorffDist2ManualRunReduceLe.lean` accumulates the reduction error along `Alg. 1`'s `manualRun`,
one `Δt`, `η` and `ρ` throughout. Eq. (28), `ε^r_{k+1} = ε^r_k + Δε^r_k(ρ_k)`, is printed with a
`ρ_k` per step, and the propagated particular solution at step `j` is `e^{At_j}P̂^U(Δt_j)` at that
step's own `Δt_j, η_j`. This is the recursion in that generality: `W j` is the zonotope `P̂^U(Δt_j)`
computed at step `j`, `Φ j` the matrix `e^{At_j}` it is propagated by, and the state `P` follows
line 10, `P̂^U(t_{j+1}) = reduce(P̂^U(t_j) ⊕ Φ_j W_j, ρ_j)`. Nothing but eq. (29) and the two facts
of the constant-parameter proof is used, so no hypothesis on `Δt_j`, `η_j` or `ρ_j` is needed.

## Inputs
* `W` – one-step zonotopes
* `Φ` – propagation matrices
* `ρ` – zonotope orders
* `P` – reduced states
* `k` – number of steps

## Hypotheses
* `h0` – reduced state starts at the origin
* `hstep` – reduced states follow the reduction recursion

## Conclusion
* the reduced accumulation is within the summed per-step reduction errors

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The unreduced accumulation of varying propagated zonotopes is compact and nonempty. -/
theorem aux_isCompact_sum_range_mulVec_var (W : ℕ → Zonotope (Vec ℝ n)) (Φ : ℕ → Mat ℝ n n)
    (k : ℕ) : -- --- CONCL ---
    IsCompact (∑ j ∈ Finset.range k, (fun x => Φ j *ᵥ x) '' (W j).construct) ∧
      (∑ j ∈ Finset.range k, (fun x => Φ j *ᵥ x) '' (W j).construct).Nonempty := by -- --- PROOF ---
  induction k with
  | zero =>
    rw [Finset.sum_range_zero, ← Set.singleton_zero]
    exact ⟨isCompact_singleton, Set.singleton_nonempty 0⟩
  | succ k ih =>
    rw [Finset.sum_range_succ]
    exact ⟨ih.1.add ((W k).isCompact_construct.image (mulVecL (Φ k)).continuous),
      ih.2.add (Set.Nonempty.image _ ⟨(W k).c, Zonotope.center_mem_construct (W k)⟩)⟩

/-- `d_H` ignores a summand both sides share: `hausdorffDist₂_add_le` at `d_H(X,X) = 0`. -/
theorem aux_hausdorffDist₂_add_right_var {S T X : Set (Vec ℝ n)} (hS : IsCompact S)
    (hSne : S.Nonempty) (hT : IsCompact T) (hTne : T.Nonempty) (hX : IsCompact X)
    (hXne : X.Nonempty) :
    hausdorffDist₂ (S + X) (T + X) ≤ hausdorffDist₂ S T := by
  have hself : hausdorffDist₂ X X = 0 := Metric.hausdorffDist_self_zero
  have h := hausdorffDist₂_add_le hS hSne hT hTne hX hXne hX hXne
  rw [hself, add_zero] at h
  exact h


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 4], eq. (28) at a `ρ_k` and a propagated `Φ_kW_k` per step: the iteratively reduced
`P̂^U(t_k)` is within the summed per-step reduction errors of the same accumulation with line 10's
`reduce` omitted. -/
theorem hausdorffDist₂_var_run_reduce_le (W : ℕ → Zonotope (Vec ℝ n)) (Φ : ℕ → Mat ℝ n n)
    (ρ : ℕ → ℕ) (P : ℕ → Zonotope (Vec ℝ n)) (h0 : (P 0).construct = {0})
    (hstep : ∀ j, P (j + 1) = Zonotope.reduce (Zonotope.plus (P j) (Zonotope.mtimes (Φ j) (W j)))
      (ρ j)) (k : ℕ) : -- --- CONCL ---
    hausdorffDist₂ (∑ j ∈ Finset.range k, (fun x => Φ j *ᵥ x) '' (W j).construct)
        (P k).construct
      ≤ ∑ j ∈ Finset.range k,
        (Zonotope.plus (P j) (Zonotope.mtimes (Φ j) (W j))).reduceBoxError
          (ρ j) := by -- --- PROOF ---
  have hsum := aux_isCompact_sum_range_mulVec_var W Φ
  induction k with
  | zero =>
    rw [Finset.sum_range_zero, Finset.sum_range_zero, h0, ← Set.singleton_zero]
    refine hausdorffDist₂_le_of_mem_dist (le_refl 0) (fun x hx => ?_) (fun x hx => ?_) <;>
      exact ⟨x, hx, by rw [sub_self, norm₂_zero]⟩
  | succ k ih =>
    have hXc : IsCompact ((fun x => Φ k *ᵥ x) '' (W k).construct) :=
      (Zonotope.isCompact_construct _).image (mulVecL _).continuous
    have hXne : ((fun x => Φ k *ᵥ x) '' (W k).construct).Nonempty :=
      Set.Nonempty.image _ ⟨_, Zonotope.center_mem_construct _⟩
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hstep k]
    refine (hausdorffDist₂_triangle ((hsum k).1.add hXc).isBounded ((hsum k).2.add hXne)
      (Zonotope.isBounded_construct _) ⟨_, Zonotope.center_mem_construct _⟩).trans
      (add_le_add ?_ (Zonotope.hausdorffDist₂_reduce_le _ (ρ k)))
    rw [← Zonotope.plus_exact, ← Zonotope.mtimes_exact]
    exact (aux_hausdorffDist₂_add_right_var (hsum k).1 (hsum k).2
      (Zonotope.isCompact_construct _) ⟨_, Zonotope.center_mem_construct _⟩ hXc hXne).trans ih

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
