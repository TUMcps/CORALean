module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.AugmentArnoldiPow
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution
public import CORALean.ContSet.Interval.Real.Theorems.MemMat
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

/-!
# The input solution for varying inputs from the Krylov Taylor terms

A correct form of [1, Thm. IV.2] for arbitrarily varying inputs in a convex, closed, bounded
`U`: `R_p(δ) ⊆ ⊕_{j=1}^{η+1} {P Ṽ(u) H̃ʲ(u) e₁ | u ∈ U} δʲ/j! ⊕ R`, with Alg. 1 run `m + 1`
passes on `C̃(u) = [A u; 0 0]`, `ṽ = [0ₙ; 1]`, and `η + 1 ≤ m`. The Taylor terms are [1]'s
`P D⁽ʲ⁾ e₁ δʲ` at its `η + 1`; the remainder `R` is not [1]'s Krylov one,
`P{Ẽ(δ, u)}e₁ ⊕ [-1, 1]ⁿ{ε̃(u)}δ`, but the closed convex hull of `E(δ)·δ·U`, the remainder of
Althoff's thesis [2, Thm. 3.1] (`inputReach_subset_inputSolution`, taken at plain sets). Below
the Krylov order each Krylov term is `A^{j-1} U δʲ/j!` (`augment_arnoldi_pow`), so the
convexity the merge (29) needs holds there. [1]'s own remainder for varying inputs is open:
its proof sums `Cor. IV.1`'s error boxes, whose radii do not add up to `ε̃δ`.

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
* [2] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The Minkowski sum of plain sets, exactly. -/
@[reducible] def Krylov.aux_setPlus (k : ℕ) : Plus (Set (Vec ℝ k)) (Vec ℝ k) :=
  ⟨fun a b => a + b, fun _ _ => le_rfl⟩

/-- A plain matrix's image of a plain set, exactly. -/
@[reducible] def Krylov.aux_setMtimes : Mtimes (Mat ℝ) 𝒮 where
  mtimes M s := (M *ᵥ ·) '' s
  mtimes_outer M s := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact le_rfl

/-- An interval matrix's images of a plain set, closed and convexified. -/
@[reducible] noncomputable def Krylov.aux_setMtimesInterval :
    Mtimes (ℐ) 𝒮 where
  mtimes I s := closure (convexHull ℝ (⋃ A ∈ construct I, (A *ᵥ ·) '' s))
  mtimes_outer _ _ := (subset_convexHull ℝ _).trans subset_closure

attribute [local instance] Krylov.aux_setPlus Krylov.aux_setMtimes Krylov.aux_setMtimesInterval

/-- The images of a bounded set under the matrices of an interval matrix are bounded. -/
theorem Krylov.aux_isBounded_iUnion_image (I : Interval (Mat ℝ n n)) {U : Set (Vec ℝ n)}
    (hU : Bornology.IsBounded U) :
    Bornology.IsBounded (⋃ M ∈ I.construct, (M *ᵥ ·) '' U) := by -- --- PROOF ---
  obtain ⟨C, hC⟩ := hU.exists_norm_le
  set c := ∑ i, ∑ j, (|I.inf i j| + |I.sup i j|) with hc
  refine isBounded_iff_forall_norm_le.2 ⟨c * |C|, fun x hx => ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image] at hx
  obtain ⟨M, hM, u, hu, rfl⟩ := hx
  have hMij : ∀ i j, |M i j| ≤ |I.inf i j| + |I.sup i j| := by
    intro i j
    obtain ⟨h1, h2⟩ := Interval.mem_mat_iff.mp hM i j
    exact abs_le.2 ⟨by linarith [neg_abs_le (I.inf i j), abs_nonneg (I.sup i j)],
      by linarith [le_abs_self (I.sup i j), abs_nonneg (I.inf i j)]⟩
  have hu' : ∀ j, |u j| ≤ |C| := fun j =>
    ((norm_le_pi_norm u j).trans (hC u hu)).trans (le_abs_self C)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  -- each coordinate is a sum of entries times coordinates, each at most its bound
  calc ‖(M *ᵥ u) i‖ = |∑ j, M i j * u j| := rfl
    _ ≤ ∑ j, |M i j| * |u j| := (Finset.abs_sum_le_sum_abs _ _).trans (by simp [abs_mul])
    _ ≤ ∑ j, (|I.inf i j| + |I.sup i j|) * |C| := Finset.sum_le_sum fun j _ =>
        mul_le_mul (hMij i j) (hu' j) (abs_nonneg _) (by positivity)
    _ = (∑ j, (|I.inf i j| + |I.sup i j|)) * |C| := (Finset.sum_mul _ _ _).symm
    _ ≤ c * |C| := by
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        exact Finset.single_le_sum (f := fun i => ∑ j, (|I.inf i j| + |I.sup i j|))
          (fun i _ => by positivity) (Finset.mem_univ i)

/-- Order `j` of the thesis' Taylor sum is the Krylov term `P Ṽ H̃^{j+1} e₁ δ^{j+1}/(j+1)!`. -/
theorem Krylov.aux_inputTerm_image_eq (A : Mat ℝ n n) (U : Set (Vec ℝ n)) (δ : ℝ) (m : ℕ)
    {j : ℕ} (hj : j + 1 ≤ m) :
    ((LinearSys.mk A : LinearSys ℝ n).inputTerm δ j *ᵥ ·) '' U
      = (fun u : Vec ℝ n => (δ ^ (j + 1) / (Nat.factorial (j + 1) : ℝ)) • fun i =>
          (Krylov.arnoldiBasis (Krylov.augment A u) (Pi.single (Fin.last n) 1) (m + 1) *ᵥ
            (Krylov.arnoldiHessenberg (Krylov.augment A u) (Pi.single (Fin.last n) 1) (m + 1)
              ^ (j + 1) *ᵥ Pi.single 0 1)) (Fin.castSucc i)) '' U := by
  refine Set.image_congr fun u _ => ?_
  rw [Krylov.augment_arnoldi_pow A u m (Nat.le_add_left 1 j) hj, Nat.add_sub_cancel,
    LinearSys.inputTerm, Matrix.smul_mulVec]
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. IV.2]'s Taylor terms for varying inputs, below the Krylov order `η + 1 ≤ m`,
with the thesis' remainder `E(δ)·δ·U` closed and convexified in place of [1]'s. -/
theorem Krylov.inputReach_subset_krylovTaylor (A : Mat ℝ n n) {U : Set (Vec ℝ n)}
    (hconv : Convex ℝ U) (hclosed : IsClosed U) (hbdd : Bornology.IsBounded U) {δ : ℝ}
    (hδ : 0 < δ) (η m : ℕ) (hηm : η + 1 ≤ m) (hε : ‖δ • A‖ / ((η : ℝ) + 2) < 1) :
    (LinearSys.mk A : LinearSys ℝ n).inputReach (S := 𝒮) U δ
      ⊆ (∑ j ∈ Finset.range (η + 1),
          (fun u : Vec ℝ n => (δ ^ (j + 1) / (Nat.factorial (j + 1) : ℝ)) • fun i =>
            (Krylov.arnoldiBasis (Krylov.augment A u) (Pi.single (Fin.last n) 1) (m + 1) *ᵥ
              (Krylov.arnoldiHessenberg (Krylov.augment A u) (Pi.single (Fin.last n) 1) (m + 1)
                ^ (j + 1) *ᵥ Pi.single 0 1)) (Fin.castSucc i)) '' U)
        + closure (convexHull ℝ
            (⋃ M ∈ (MatExp.inputRemainder A δ η).construct, (M *ᵥ ·) '' U)) := by -- --- PROOF ---
  have hR := Krylov.aux_isBounded_iUnion_image (MatExp.inputRemainder A δ η) hbdd
  -- the thesis' enclosure, at plain sets
  have hexact := (LinearSys.mk A : LinearSys ℝ n).inputReach_subset_inputSolution
    (S := 𝒮) hδ η hε (U := U) hconv hclosed hbdd
    (convex_convexHull ℝ _).closure isClosed_closure (isBounded_convexHull.2 hR).closure
  refine hexact.trans ?_
  unfold LinearSys.inputSolution
  refine Set.add_subset_add ?_ le_rfl
  -- its Taylor sum, one order at a time, is the sum of the Krylov terms
  suffices h : ∀ i ≤ η, construct ((LinearSys.mk A : LinearSys ℝ n).inputTaylorSum
      (S := 𝒮) δ U i)
      ⊆ ∑ j ∈ Finset.range (i + 1),
          (fun u : Vec ℝ n => (δ ^ (j + 1) / (Nat.factorial (j + 1) : ℝ)) • fun i =>
            (Krylov.arnoldiBasis (Krylov.augment A u) (Pi.single (Fin.last n) 1) (m + 1) *ᵥ
              (Krylov.arnoldiHessenberg (Krylov.augment A u) (Pi.single (Fin.last n) 1) (m + 1)
                ^ (j + 1) *ᵥ Pi.single 0 1)) (Fin.castSucc i)) '' U from h η le_rfl
  intro i hi
  induction i with
  | zero =>
    rw [Finset.sum_range_one, ← Krylov.aux_inputTerm_image_eq A U δ m (by omega)]
    exact le_rfl
  | succ i ih =>
    rw [Finset.sum_range_succ, ← Krylov.aux_inputTerm_image_eq A U δ m (by omega)]
    exact Set.add_subset_add (ih (by omega)) le_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
