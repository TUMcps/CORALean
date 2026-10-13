import CORALean.ContDynamics.LinearSysDT.Definitions.IsConformDyn
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# A model that produced the data is never rejected

If every test case `i` is a run of the system `x(k+1) = A x(k) + B u(k) + c + E w(k)`,
`y(k) = C x(k) + D u(k) + k + F v(k)` with `x(0) - x0 ∈ X₀`, `w ∈ W`, `v ∈ V`, then
`isconform_dyn` returns `true`, at every horizon [1]: the deviation from the nominal run is
`C A^k (x(0) - x0) + ∑ C A^{k-1-l} E w(l) + F v(k)`, one member of each summand of `R_k`. Only
that: `true` is no proof that one run explains all samples of a test case, the check being
one sample at a time.

## References

* [1] `contDynamics/@linearSysDT/isconform_dyn.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes

variable {n m q s r : ℕ} {ι : Type}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The state deviation from the nominal run: the initial one carried through, and the
disturbances. -/
theorem aux_conform_delta (sys : LinearSysDT ℝ n) (B : Mat ℝ n m) (c : Vec ℝ n)
    (E : Mat ℝ n q) (x0 : Vec ℝ n) (u : ℕ → Vec ℝ m) {x : ℕ → Vec ℝ n} {w : ℕ → Vec ℝ q}
    (hx : ∀ j, x (j + 1) = sys.A *ᵥ x j + B *ᵥ u j + c + E *ᵥ w j) (j : ℕ) :
    x j - sys.nominalState B c x0 u j
      = sys.A ^ j *ᵥ (x 0 - x0)
        + ∑ l ∈ Finset.range j, (sys.A ^ (j - 1 - l) * E) *ᵥ w l := by -- --- PROOF ---
  induction j with
  | zero => simp [LinearSysDT.nominalState]
  | succ j ih =>
    -- one step: the deviation is `A` times the last one plus `E w`
    have hstep : x (j + 1) - sys.nominalState B c x0 u (j + 1)
        = sys.A *ᵥ (x j - sys.nominalState B c x0 u j) + E *ᵥ w j := by
      rw [hx, LinearSysDT.nominalState, Matrix.mulVec_sub]
      abel
    rw [hstep, ih, Finset.sum_range_succ, Matrix.mulVec_add, Matrix.mulVec_sum, mulVec_mulVec]
    have hsum : ∑ l ∈ Finset.range j, sys.A *ᵥ ((sys.A ^ (j - 1 - l) * E) *ᵥ w l)
        = ∑ l ∈ Finset.range j, (sys.A ^ (j + 1 - 1 - l) * E) *ᵥ w l := by
      refine Finset.sum_congr rfl fun l hl => ?_
      have hl' := Finset.mem_range.mp hl
      rw [mulVec_mulVec, ← Matrix.mul_assoc, ← pow_succ']
      congr 3
      omega
    rw [hsum, ← pow_succ', Nat.add_sub_cancel, Nat.sub_self, pow_zero, Matrix.one_mul]
    abel

/-- The disturbances' part of the deviation set holds the sum, one member of `W` per term. -/
theorem aux_conform_add (sys : LinearSysDT ℝ n) (C : Mat ℝ r n) (E : Mat ℝ n q) (W : S q)
    (ω : ℕ → Vec ℝ q) (hω : ∀ j, ω j ∈ construct W) (k : ℕ) :
    ∑ j ∈ Finset.range k, (C * sys.A ^ j) *ᵥ (E *ᵥ ω j)
      ∈ construct (sys.conformAdd C E W k) := by -- --- PROOF ---
  induction k with
  | zero =>
    -- the empty sum is `0`, the point
    simpa [LinearSysDT.conformAdd] using OfPoint.mem_ofPoint (S := S r) (0 : Vec ℝ r)
  | succ k ih =>
    -- the new term, a member of `C A^k (E W)`
    rw [Finset.sum_range_succ]
    refine Plus.plus_outer _ _ (Set.add_mem_add ih ?_)
    refine Mtimes.mtimes_outer _ _ ?_
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    refine Set.mem_image_of_mem _ (Mtimes.mtimes_outer _ _ ?_)
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact Set.mem_image_of_mem _ (hω k)


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.isConformDyn_of_model (sys : LinearSysDT ℝ n) (B : Mat ℝ n m) (c : Vec ℝ n)
    (out : OutputEq ℝ n m r) (kk : Vec ℝ r) (E : Mat ℝ n q) (F : Mat ℝ r s) (X₀ : S n)
    (W : S q) (V : S s) (K : ℕ) (x0 : ι → Vec ℝ n) (u : ι → ℕ → Vec ℝ m) (y : ι → ℕ → Vec ℝ r)
    (hmodel : ∀ i, ∃ (x : ℕ → Vec ℝ n) (w : ℕ → Vec ℝ q) (v : ℕ → Vec ℝ s),
      x 0 - x0 i ∈ construct X₀ ∧ (∀ j, w j ∈ construct W) ∧ (∀ j, v j ∈ construct V) ∧
      (∀ j, x (j + 1) = sys.A *ᵥ x j + B *ᵥ u i j + c + E *ᵥ w j) ∧
      ∀ j, y i j = out.eval (x j) (u i j) + kk + F *ᵥ v j) :
    sys.IsConformDyn B c out kk E F X₀ W V K x0 u y := by -- --- PROOF ---
  intro i k _
  obtain ⟨x, w, v, hx0, hw, hv, hx, hy⟩ := hmodel i
  have hdelta := aux_conform_delta sys B c E (x0 i) (u i) hx k
  -- the deviation of the output is `C δ(k) + F v(k)`
  have hdev : y i k - (out.eval (sys.nominalState B c (x0 i) (u i) k) (u i k) + kk)
      = (out.C * sys.A ^ k) *ᵥ (x 0 - x0 i)
        + ∑ l ∈ Finset.range k, (out.C * sys.A ^ (k - 1 - l)) *ᵥ (E *ᵥ w l) + F *ᵥ v k := by
    rw [hy k]
    simp only [OutputEq.eval, Scalar.toRealMat_real]
    have h := congrArg (fun z => out.C *ᵥ z) hdelta
    simp only [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_sum, mulVec_mulVec,
      Matrix.mul_assoc] at h ⊢
    -- the disturbances' terms, as `C A^j (E w)`
    have hsum : ∑ l ∈ Finset.range k, (out.C * (sys.A ^ (k - 1 - l) * E)) *ᵥ w l
        = ∑ l ∈ Finset.range k, (out.C * sys.A ^ (k - 1 - l)) *ᵥ (E *ᵥ w l) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [mulVec_mulVec, Matrix.mul_assoc]
    rw [hsum] at h ⊢
    linear_combination (norm := module) h
  rw [hdev]
  -- one member of each summand of `R_k`, the disturbances' terms read in the other order
  have hadd := aux_conform_add sys out.C E W (fun j => w (k - 1 - j)) (fun j => hw _) k
  have hre : ∑ l ∈ Finset.range k, (out.C * sys.A ^ (k - 1 - l)) *ᵥ (E *ᵥ w l)
      = ∑ j ∈ Finset.range k, (out.C * sys.A ^ j) *ᵥ (E *ᵥ w (k - 1 - j)) := by
    rw [← Finset.sum_range_reflect (fun j => (out.C * sys.A ^ j) *ᵥ (E *ᵥ w (k - 1 - j))) k]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' := Finset.mem_range.mp hl
    simp only [show k - 1 - (k - 1 - l) = l by omega]
  rw [hre]
  refine Plus.plus_outer _ _ (Set.add_mem_add (Plus.plus_outer _ _ (Set.add_mem_add ?_ hadd)) ?_)
  · refine Mtimes.mtimes_outer _ _ ?_
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact Set.mem_image_of_mem _ hx0
  · refine Mtimes.mtimes_outer _ _ ?_
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact Set.mem_image_of_mem _ (hv k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
