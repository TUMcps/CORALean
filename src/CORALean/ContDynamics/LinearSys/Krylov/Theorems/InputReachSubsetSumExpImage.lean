import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationSubset

/-!
# The input part of Alg. 2, with the exponent of (24)

[1, Alg. 2] keeps the input solution as `R_{p,k+1} = R_{p,k} ⊕ box(R*_{b,k+1})` (line 9), from
`R_{p,1} = box(conv(0ₙ, R*_{b,1}))` (line 3), `R*_{b,1} ⊇ R_p(δ)` (line 2). With
`R*_{b,k+1} ⊇ e^{Akδ} R*_{b,1}`, (24)'s `e^{At_k}` at `t_k = kδ`, this encloses the input
solution on `[kδ, (k + 1)δ]`: `R_p(kδ + s) ⊆ ⊕_{i=0}^{k} e^{Aiδ} R_p(δ)` for `s ∈ [0, δ]`, and each
term lies in the box of the matching `R*_{b,i+1}`. One step of [2, Prop. 3.2]
(`inputReach_separation_subset`) per `k`, and [2, Prop. 3.3] (`inputReach_mono`, `0 ∈ U`) for
the part of the step before `δ`. Line 8 as printed takes `e^{A(k+1)δ}`, one step too many
(`printed_input_propagation_counterexample`).

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
* [2] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A matrix maps a finite Minkowski sum into the sum of the images. -/
theorem Krylov.aux_image_sum_subset (M : Mat ℝ n n) (F : ℕ → Set (Vec ℝ n)) (p : ℕ) :
    (M *ᵥ ·) '' (∑ i ∈ Finset.range p, F i)
      ⊆ ∑ i ∈ Finset.range p, (M *ᵥ ·) '' F i := by -- --- PROOF ---
  induction p with
  | zero =>
    rintro _ ⟨y, hy, rfl⟩
    rw [Finset.sum_range_zero, Set.mem_zero] at hy ⊢
    rw [hy]
    exact mulVec_zero M
  | succ p ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h := Set.image_add (Matrix.mulVecLin M) (s := ∑ i ∈ Finset.range p, F i) (t := F p)
    simp only [Matrix.coe_mulVecLin] at h
    rw [h]
    exact Set.add_subset_add ih le_rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- `R_p(kδ + s) ⊆ ⊕_{i=0}^{k} e^{Aiδ} R_p(δ)` for `s ∈ [0, δ]`, `0 ∈ U`: Alg. 2's input part
with (24)'s exponent. -/
theorem Krylov.inputReach_subset_sum_exp_image (sys : LinearSys 𝕋 n) {U : S n}
    (hbdd : Bornology.IsBounded (construct U)) (h0 : (0 : Vec ℝ n) ∈ construct U) {δ : ℝ}
    (hδ : 0 ≤ δ) (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hsδ : s ≤ δ) :
    sys.inputReach U (k * δ + s)
      ⊆ ∑ i ∈ Finset.range (k + 1),
          (fun y => exp ((i * δ) • toRealMat sys.A) *ᵥ y)
            '' sys.inputReach U δ := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  induction k with
  | zero =>
    -- the part of the first step before `δ`, at `e^{A·0} = I`
    rw [Finset.sum_range_one, Nat.cast_zero, zero_mul, zero_smul, exp_zero, zero_add]
    simp only [one_mulVec, Set.image_id']
    exact sys.inputReach_mono hbdd h0 hs0 hsδ
  | succ k ih =>
    -- one more step: the earlier ones propagated by `e^{Aδ}`, plus a step of its own
    have hsplit : ((k + 1 : ℕ) : ℝ) * δ + s = (k * δ + s) + δ := by push_cast; ring
    rw [hsplit]
    refine (sys.inputReach_separation_subset (by positivity) hδ hbdd).trans ?_
    rw [Finset.sum_range_succ']
    refine Set.add_subset_add ?_ ?_
    · refine (Set.image_mono ih).trans ((Krylov.aux_image_sum_subset _ _ _).trans ?_)
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Set.image_image]
      refine le_of_eq (Set.image_congr fun y _ => ?_)
      have hc : Commute (δ • A) ((i * δ) • A) := ((Commute.refl A).smul_left δ).smul_right _
      have hmul : exp (δ • A) * exp ((i * δ) • A) = exp ((((i + 1 : ℕ) : ℝ) * δ) • A) := by
        rw [show ((i + 1 : ℕ) : ℝ) * δ = δ + i * δ by push_cast; ring, add_smul]
        exact (exp_add_of_commute hc).symm
      rw [← hA, mulVec_mulVec, hmul]
    · rw [Nat.cast_zero, zero_mul, zero_smul, exp_zero]
      simp only [one_mulVec, Set.image_id']
      exact le_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
