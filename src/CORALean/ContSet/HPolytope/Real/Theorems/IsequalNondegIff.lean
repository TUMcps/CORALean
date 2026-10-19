module

public import CORALean.ContSet.HPolytope.Real.Operations.IsequalNondeg
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.ExistsPosStepStrict
public import CORALean.ContSet.ContSet.Theorems.SupportFuncLeCoeIff
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Tactic.FieldSimp
public import Mathlib.LinearAlgebra.Matrix.DotProduct

@[expose] public section

/-!
# `HPolytope.isequalNondeg` decides equality

[1, Alg. 1]: for two non-degenerate H-polytopes in minimal representation, without zero rows,
the test answers `true` exactly when the polytopes are equal. "Only if" is the easy half: in a
minimal representation no row is redundant, so every row has an equal row on the other side and
each polytope lies in the other. "If" is that a non-degenerate polytope determines its normalized
facet rows: a row `a` of a minimal representation is tight, alone, at some point `z` reached from
an interior point towards a point the row cuts off; some row `a'` of the other representation is
tight at `z` too, or a step along `a` would stay inside; and `a'` then bounds every direction `a`
bounds, so the unit vectors agree.

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {q q' q₁ q₂ n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A row tight at an interior point would let a step along it leave the polytope. -/
theorem aux_strict_of_interior (A : Mat ℝ q n) (b : Vec ℝ q) (hA : ∀ i, A i ⬝ᵥ A i = 1)
    {x : Vec ℝ n} (hx : x ∈ interior (HPolytope.ineqs A b).construct) (i : Fin q) :
    (A *ᵥ x) i < b i := by -- --- PROOF ---
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  set t := ε / (2 * (‖A i‖ + 1)) with ht
  have htpos : 0 < t := by positivity
  have hmem : x + t • A i ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos htpos, ht]
    have hn := norm_nonneg (A i)
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hrow := HPolytope.mem_ineqs_iff.mp (hball hmem) i
  have hcalc : (A *ᵥ (x + t • A i)) i = (A *ᵥ x) i + t := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    show (A *ᵥ x) i + t * (A i ⬝ᵥ A i) = _
    rw [hA i, mul_one]
  linarith

/-- Unit vectors bounding the same directions are equal. -/
theorem aux_eq_of_dir {a a' : Vec ℝ n} (ha : a ⬝ᵥ a = 1) (ha' : a' ⬝ᵥ a' = 1)
    (h : ∀ d : Vec ℝ n, a ⬝ᵥ d ≤ 0 → a' ⬝ᵥ d ≤ 0) : a' = a := by -- --- PROOF ---
  set μ := a' ⬝ᵥ a with hμ
  have hμ' : a ⬝ᵥ a' = μ := dotProduct_comm _ _
  -- `a' - μ a` is orthogonal to `a`, so `a'` vanishes on it from both sides
  have hd : a ⬝ᵥ (a' - μ • a) = 0 := by
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, ha, hμ', mul_one, sub_self]
  have h1 := h (a' - μ • a) hd.le
  have h2 := h (-(a' - μ • a)) (by rw [dotProduct_neg, hd, neg_zero])
  rw [dotProduct_neg] at h2
  have hzero : a' ⬝ᵥ (a' - μ • a) = 0 := by linarith
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, ha', ← hμ] at hzero
  -- `a'` bounds `-a`, so `μ ≥ 0`, hence `μ = 1`
  have h3 := h (-a) (by rw [dotProduct_neg, ha]; norm_num)
  rw [dotProduct_neg, ← hμ] at h3
  have hμ1 : μ = 1 := by nlinarith
  have hsq : (a' - a) ⬝ᵥ (a' - a) = 0 := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, ha, ha', ← hμ, hμ', hμ1]
    ring
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hsq)

/-- A non-redundant row of a non-degenerate polytope is a row of every representation. -/
theorem aux_facet (A : Mat ℝ q n) (b : Vec ℝ q) (A' : Mat ℝ q' n) (b' : Vec ℝ q')
    (hA : ∀ i, A i ⬝ᵥ A i = 1) (hA' : ∀ k, A' k ⬝ᵥ A' k = 1)
    (hint : (interior (HPolytope.ineqs A b).construct).Nonempty) (j : Fin q)
    (hred : (HPolytope.ineqs A b).construct ≠
      (HPolytope.ineqs (A.submatrix (dropIdx j) id) fun i => b (dropIdx j i)).construct)
    (heq : (HPolytope.ineqs A b).construct = (HPolytope.ineqs A' b').construct) : -- --- CONCL ---
    ∃ k, A' k = A j ∧ b' k = b j := by -- --- PROOF ---
  -- a point kept by the other rows and cut off by row `j`
  have hsub : (HPolytope.ineqs A b).construct ⊆ (HPolytope.ineqs (A.submatrix (dropIdx j) id)
      fun i => b (dropIdx j i)).construct := fun x hx =>
    HPolytope.mem_ineqs_iff.mpr fun i => HPolytope.mem_ineqs_iff.mp hx (dropIdx j i)
  obtain ⟨y, hyD, hyP⟩ := Set.exists_of_ssubset (ssubset_of_subset_of_ne hsub hred)
  have hyrows := HPolytope.mem_ineqs_iff.mp hyD
  have hyj : b j < (A *ᵥ y) j := by
    by_contra hle
    refine hyP (HPolytope.mem_ineqs_iff.mpr fun l => ?_)
    revert l
    exact (forall_dropIdx_iff j).mpr ⟨not_lt.mp hle, fun i => hyrows i⟩
  obtain ⟨x, hx⟩ := hint
  have hxs := aux_strict_of_interior A b hA hx
  -- the point of the segment where row `j` becomes tight
  set t := (b j - (A *ᵥ x) j) / ((A *ᵥ y) j - (A *ᵥ x) j) with ht
  have hden : 0 < (A *ᵥ y) j - (A *ᵥ x) j := by linarith [hxs j]
  have ht0 : 0 < t := div_pos (by linarith [hxs j]) hden
  have ht1 : t < 1 := by rw [div_lt_one hden]; linarith
  set z := x + t • (y - x) with hz
  have hzi : ∀ i, (A *ᵥ z) i = (A *ᵥ x) i + t * ((A *ᵥ y) i - (A *ᵥ x) i) := fun i => by
    simp only [hz, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have hzj : (A *ᵥ z) j = b j := by
    rw [hzi, ht]
    field_simp
    ring
  -- every other row stays strict at `z`
  have hzo : ∀ i, (A *ᵥ z) (dropIdx j i) < b (dropIdx j i) := fun i => by
    rw [hzi]
    have := hyrows i
    have hxi := hxs (dropIdx j i)
    have : (A *ᵥ y) (dropIdx j i) = ((A.submatrix (dropIdx j) id) *ᵥ y) i := rfl
    nlinarith
  have hzP : z ∈ (HPolytope.ineqs A b).construct := by
    refine HPolytope.mem_ineqs_iff.mpr fun l => ?_
    revert l
    exact (forall_dropIdx_iff j).mpr ⟨hzj.le, fun i => (hzo i).le⟩
  -- the rows of `A` with row `j` relaxed by one hold strictly at `z`
  have hzs : ∀ i, (A *ᵥ z) i < (Function.update b j (b j + 1)) i := by
    intro l
    revert l
    refine (forall_dropIdx_iff j).mpr ⟨by rw [Function.update_self, hzj]; linarith, fun i => ?_⟩
    have hne : dropIdx j i ≠ j := fun h => by
      have := insertIdx_dropIdx j true (fun _ => false) i
      rw [h, insertIdx_self] at this
      exact Bool.noConfusion this
    rw [Function.update_of_ne hne]
    exact hzo i
  -- some row of the other representation is tight at `z`
  have hzP' := heq ▸ hzP
  obtain ⟨k, hk⟩ : ∃ k, (A' *ᵥ z) k = b' k := by
    by_contra hnone
    push Not at hnone
    have hlt : ∀ k, (A' *ᵥ z) k < b' k := fun k =>
      lt_of_le_of_ne (HPolytope.mem_ineqs_iff.mp hzP' k) (hnone k)
    obtain ⟨s, hs, hsA⟩ := HPolytope.exists_pos_step_strict A' b' z (A j) hlt
    have hmem : z + s • A j ∈ (HPolytope.ineqs A b).construct :=
      heq ▸ HPolytope.mem_ineqs_iff.mpr fun k => (hsA k).le
    have hrow := HPolytope.mem_ineqs_iff.mp hmem j
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hzj]
      at hrow
    have : (A *ᵥ A j) j = 1 := hA j
    rw [this] at hrow
    linarith
  -- that row bounds every direction row `j` bounds
  have hdir : ∀ d : Vec ℝ n, A j ⬝ᵥ d ≤ 0 → A' k ⬝ᵥ d ≤ 0 := by
    intro d hd
    obtain ⟨s, hs, hsA⟩ := HPolytope.exists_pos_step_strict A _ z d hzs
    have hmem : z + s • d ∈ (HPolytope.ineqs A b).construct := by
      refine HPolytope.mem_ineqs_iff.mpr fun l => ?_
      revert l
      refine (forall_dropIdx_iff j).mpr ⟨?_, fun i => ?_⟩
      · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hzj]
        have : (A *ᵥ d) j = A j ⬝ᵥ d := rfl
        nlinarith
      -- the other rows: strict at the step, by its choice
      · have := hsA (dropIdx j i)
        have hne : dropIdx j i ≠ j := fun h => by
          have := insertIdx_dropIdx j true (fun _ => false) i
          rw [h, insertIdx_self] at this
          exact Bool.noConfusion this
        rw [Function.update_of_ne hne] at this
        exact this.le
    -- row `k` of the other representation, tight at `z`, holds at the step
    have hrow := HPolytope.mem_ineqs_iff.mp (heq ▸ hmem) k
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hk]
      at hrow
    have : (A' *ᵥ d) k = A' k ⬝ᵥ d := rfl
    nlinarith
  have hkj := aux_eq_of_dir (hA j) (hA' k) hdir
  refine ⟨k, hkj, ?_⟩
  rw [← hk, ← hzj]
  show A' k ⬝ᵥ z = A j ⬝ᵥ z
  rw [hkj]

/-- Line 1 leaves the set alone. -/
theorem aux_normalize (A : Mat ℝ q n) (b : Vec ℝ q) (hA : ∀ i, A i ≠ 0) :
    (HPolytope.ineqs (Matrix.of fun j => ‖A j‖₂⁻¹ • A j) fun j => b j / ‖A j‖₂).construct =
      (HPolytope.ineqs A b).construct := by -- --- PROOF ---
  have hpos : ∀ j, 0 < ‖A j‖₂ := fun j => by
    rcases (norm₂_nonneg (A j)).eq_or_lt with h | h
    · exfalso
      apply hA j
      rw [← dotProduct_self_eq_zero, dotProduct_self, ← h]
      ring
    · exact h
  ext x
  rw [HPolytope.mem_ineqs_iff, HPolytope.mem_ineqs_iff]
  refine forall_congr' fun j => ?_
  have : ((Matrix.of fun j => ‖A j‖₂⁻¹ • A j) *ᵥ x) j = ‖A j‖₂⁻¹ * (A *ᵥ x) j := by
    show (‖A j‖₂⁻¹ • A j) ⬝ᵥ x = ‖A j‖₂⁻¹ * (A j ⬝ᵥ x)
    rw [smul_dotProduct, smul_eq_mul]
  rw [this, div_eq_inv_mul, mul_le_mul_iff_of_pos_left (inv_pos.mpr (hpos j))]

/-- Normalized rows have unit length. -/
theorem aux_unit (A : Mat ℝ q n) (hA : ∀ i, A i ≠ 0) (j : Fin q) :
    (Matrix.of fun j => ‖A j‖₂⁻¹ • A j : Mat ℝ q n) j ⬝ᵥ
      (Matrix.of fun j => ‖A j‖₂⁻¹ • A j : Mat ℝ q n) j = 1 := by -- --- PROOF ---
  have hpos : 0 < ‖A j‖₂ := by
    rcases (norm₂_nonneg (A j)).eq_or_lt with h | h
    · exfalso
      apply hA j
      rw [← dotProduct_self_eq_zero, dotProduct_self, ← h]
      ring
    · exact h
  show (‖A j‖₂⁻¹ • A j) ⬝ᵥ (‖A j‖₂⁻¹ • A j) = 1
  rw [smul_dotProduct, dotProduct_smul, dotProduct_self, smul_eq_mul, smul_eq_mul]
  field_simp

/-- A row is redundant, in the support-function sense of line 4, exactly when dropping it
leaves the set. -/
theorem aux_redundant_iff (A : Mat ℝ q n) (b : Vec ℝ q) (j : Fin q) : -- --- CONCL ---
    supportFunc (HPolytope.ineqs (A.submatrix (dropIdx j) id) fun i => b (dropIdx j i)).construct
        (HPolytope.rowLin A j) ≤ (b j : EReal) ↔
      (HPolytope.ineqs A b).construct =
        (HPolytope.ineqs (A.submatrix (dropIdx j) id)
          fun i => b (dropIdx j i)).construct := by -- --- PROOF ---
  rw [supportFunc_le_coe_iff]
  constructor
  · intro h
    refine Set.Subset.antisymm (fun x hx => HPolytope.mem_ineqs_iff.mpr fun i =>
      HPolytope.mem_ineqs_iff.mp hx (dropIdx j i)) fun x hx => ?_
    refine HPolytope.mem_ineqs_iff.mpr fun l => ?_
    revert l
    exact (forall_dropIdx_iff j).mpr ⟨h x hx, fun i => HPolytope.mem_ineqs_iff.mp hx i⟩
  · intro h x hx
    rw [← h] at hx
    exact HPolytope.mem_ineqs_iff.mp hx j


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.isequalNondeg_iff (A₁ : Mat ℝ q₁ n) (b₁ : Vec ℝ q₁) (A₂ : Mat ℝ q₂ n)
    (b₂ : Vec ℝ q₂) (h₁ : ∀ j, A₁ j ≠ 0) (h₂ : ∀ k, A₂ k ≠ 0)
    (hint₁ : (interior (HPolytope.ineqs A₁ b₁).construct).Nonempty)
    (hint₂ : (interior (HPolytope.ineqs A₂ b₂).construct).Nonempty)
    (hmin₁ : ∀ j, (HPolytope.ineqs A₁ b₁).construct ≠
      (HPolytope.ineqs (A₁.submatrix (dropIdx j) id) fun i => b₁ (dropIdx j i)).construct)
    (hmin₂ : ∀ k, (HPolytope.ineqs A₂ b₂).construct ≠
      (HPolytope.ineqs (A₂.submatrix (dropIdx k) id) fun i => b₂ (dropIdx k i)).construct) :
    HPolytope.isequalNondeg A₁ b₁ A₂ b₂ = true ↔
      (HPolytope.ineqs A₁ b₁).construct = (HPolytope.ineqs A₂ b₂).construct := by -- --- PROOF ---
  -- the normalized polytopes, and their dropped versions, are the originals
  have hN₁ := aux_normalize A₁ b₁ h₁
  have hN₂ := aux_normalize A₂ b₂ h₂
  have hD₁ : ∀ j, (HPolytope.ineqs ((Matrix.of fun j => ‖A₁ j‖₂⁻¹ • A₁ j).submatrix (dropIdx j) id)
      fun i => b₁ (dropIdx j i) / ‖A₁ (dropIdx j i)‖₂).construct =
      (HPolytope.ineqs (A₁.submatrix (dropIdx j) id) fun i => b₁ (dropIdx j i)).construct :=
    fun j => aux_normalize (A₁.submatrix (dropIdx j) id) _ fun i => h₁ _
  have hD₂ : ∀ k, (HPolytope.ineqs ((Matrix.of fun k => ‖A₂ k‖₂⁻¹ • A₂ k).submatrix (dropIdx k) id)
      fun i => b₂ (dropIdx k i) / ‖A₂ (dropIdx k i)‖₂).construct =
      (HPolytope.ineqs (A₂.submatrix (dropIdx k) id) fun i => b₂ (dropIdx k i)).construct :=
    fun k => aux_normalize (A₂.submatrix (dropIdx k) id) _ fun i => h₂ _
  -- each row of one list being a row of the other puts the other inside
  have hrows : ∀ {p r : ℕ} (C : Mat ℝ p n) (c : Vec ℝ p) (C' : Mat ℝ r n) (c' : Vec ℝ r),
      (∀ j, ∃ k, C j = C' k ∧ c j = c' k) →
        (HPolytope.ineqs C' c').construct ⊆ (HPolytope.ineqs C c).construct := by
    intro p r C c C' c' h x hx
    refine HPolytope.mem_ineqs_iff.mpr fun j => ?_
    obtain ⟨k, hCk, hck⟩ := h j
    have := HPolytope.mem_ineqs_iff.mp hx k
    have hrow : (C *ᵥ x) j = (C' *ᵥ x) k := by
      show C j ⬝ᵥ x = C' k ⬝ᵥ x
      rw [hCk]
    rw [hrow, hck]
    exact this
  unfold HPolytope.isequalNondeg
  simp only [Bool.if_false_right, Bool.and_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hp₁, hp₂⟩
    -- no row is redundant, so every row is matched
    have hm₁ : ∀ j, ∃ k, (Matrix.of fun j => ‖A₁ j‖₂⁻¹ • A₁ j : Mat ℝ q₁ n) j =
        (Matrix.of fun k => ‖A₂ k‖₂⁻¹ • A₂ k : Mat ℝ q₂ n) k ∧
        b₁ j / ‖A₁ j‖₂ = b₂ k / ‖A₂ k‖₂ := fun j => (hp₁ j).resolve_right fun hr =>
      hmin₁ j (by rw [← hN₁, ← hD₁ j]; exact (aux_redundant_iff _ _ j).mp hr)
    have hm₂ : ∀ k, ∃ j, (Matrix.of fun k => ‖A₂ k‖₂⁻¹ • A₂ k : Mat ℝ q₂ n) k =
        (Matrix.of fun j => ‖A₁ j‖₂⁻¹ • A₁ j : Mat ℝ q₁ n) j ∧
        b₂ k / ‖A₂ k‖₂ = b₁ j / ‖A₁ j‖₂ := fun k => (hp₂ k).resolve_right fun hr =>
      hmin₂ k (by rw [← hN₂, ← hD₂ k]; exact (aux_redundant_iff _ _ k).mp hr)
    rw [← hN₁, ← hN₂]
    exact Set.Subset.antisymm (hrows _ _ _ _ hm₂) (hrows _ _ _ _ hm₁)
  · intro heq
    -- every row of either is a facet row of the other
    have heqN : (HPolytope.ineqs (Matrix.of fun j => ‖A₁ j‖₂⁻¹ • A₁ j)
        fun j => b₁ j / ‖A₁ j‖₂).construct = (HPolytope.ineqs (Matrix.of fun k => ‖A₂ k‖₂⁻¹ • A₂ k)
        fun k => b₂ k / ‖A₂ k‖₂).construct := by rw [hN₁, hN₂, heq]
    refine ⟨fun j => Or.inl ?_, fun k => Or.inl ?_⟩
    · obtain ⟨k, hk, hb⟩ := aux_facet _ _ _ _ (aux_unit A₁ h₁) (aux_unit A₂ h₂)
        (by rw [hN₁]; exact hint₁) j (by rw [hN₁, hD₁ j]; exact hmin₁ j) heqN
      exact ⟨k, hk.symm, hb.symm⟩
    · obtain ⟨j, hj, hb⟩ := aux_facet _ _ _ _ (aux_unit A₂ h₂) (aux_unit A₁ h₁)
        (by rw [hN₂]; exact hint₂) k (by rw [hN₂, hD₂ k]; exact hmin₂ k) heqN.symm
      exact ⟨j, hj.symm, hb.symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
