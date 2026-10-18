module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.Alg2Corrected
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.InputReachSubsetSumExpImage
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# Alg. 2, repaired, encloses the reachable set

[1, Alg. 2] with line 8 at `e^{Akδ}` and line 10's `theorem_III.2` given its own end set
(`alg2Corrected`) encloses every `e^{At}x₀ + y`, `x₀ ∈ X₀`, `y ∈ R_p(t)`, `t ∈ [0, t_f]`, given
what its subroutines are proved to deliver: `theorem_III.1 X t ⊇ e^{At}X` (`Thm. III.1`,
`image_subset_of_approx`), `corollary_IV.2 ⊇ R_p(δ)` (`Cor. IV.2` corrected,
`inputReach_subset_krylovZonotope`), and `theorem_III.2 X (theorem_III.1 X δ) ⊇ e^{At}X` on
`[0, δ]` (`Thm. III.2` corrected, `timeInterval_subset`); and `0 ∈ U`, which line 3's
`conv(0ₙ, R*_{b,1})` presumes. The pass for `k` covers `[kδ, (k + 1)δ]`: the homogeneous part
from `R*_{h,k} ⊇ e^{Akδ}X₀`, the input part as `⊕_{i ≤ k} e^{Aiδ}R_p(δ)`
(`inputReach_subset_sum_exp_image`), each term inside the box of the matching `R*_{b,i+1}`.

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `e^{(a + b)A} x = e^{bA} e^{aA} x`. -/
theorem Krylov.aux_exp_add_mulVec (A : Mat ℝ n n) (a b : ℝ) (x : Vec ℝ n) :
    exp ((a + b) • A) *ᵥ x = exp (b • A) *ᵥ (exp (a • A) *ᵥ x) := by -- --- PROOF ---
  have hc : Commute (b • A) (a • A) := ((Commute.refl A).smul_left b).smul_right a
  have h := (exp_add_of_commute hc).symm
  rw [add_comm a b, add_smul, mulVec_mulVec]
  rw [← add_smul] at h ⊢
  exact congrArg (· *ᵥ x) h.symm

/-- The time `t ∈ [0, t_f]` lies in the step `[mδ, (m + 1)δ]` of some pass `m < ⌈t_f/δ⌉`. -/
theorem Krylov.aux_exists_step {δ tf t : ℝ} (hδ : 0 < δ) (htf : 0 < tf) (ht : t ∈ Set.Icc 0 tf) :
    ∃ m < ⌈tf / δ⌉₊, ∃ s ∈ Set.Icc 0 δ, t = m * δ + s := by -- --- PROOF ---
  have hK : 0 < ⌈tf / δ⌉₊ := Nat.ceil_pos.2 (div_pos htf hδ)
  have hle : ⌈t / δ⌉₊ ≤ ⌈tf / δ⌉₊ := Nat.ceil_mono (div_le_div_of_nonneg_right ht.2 hδ.le)
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · exact ⟨0, hK, 0, ⟨le_rfl, hδ.le⟩, by rw [← h0]; simp⟩
  -- `m = ⌈t/δ⌉ - 1`, so `mδ < t ≤ (m + 1)δ`
  have hc : 0 < ⌈t / δ⌉₊ := Nat.ceil_pos.2 (div_pos hpos hδ)
  refine ⟨⌈t / δ⌉₊ - 1, by omega, t - (⌈t / δ⌉₊ - 1 : ℕ) * δ, ⟨?_, ?_⟩, by ring⟩
  · have h1 := Nat.ceil_lt_add_one (div_pos hpos hδ).le
    rw [Nat.cast_sub hc, Nat.cast_one]
    have : ((⌈t / δ⌉₊ : ℝ) - 1) < t / δ := by linarith
    have := (lt_div_iff₀ hδ).1 this
    linarith
  · have h1 := Nat.le_ceil (t / δ)
    rw [Nat.cast_sub hc, Nat.cast_one]
    have := (div_le_iff₀ hδ).1 h1
    linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2] with lines 8 and 10 repaired encloses `e^{At}x₀ + R_p(t)` for `t ∈ [0, t_f]`,
given its subroutines' enclosures and `0 ∈ U`. -/
theorem Krylov.reach_subset_alg2Corrected (A : Mat ℝ n n) {U : Set (Vec ℝ n)}
    (hbdd : Bornology.IsBounded U) (h0 : (0 : Vec ℝ n) ∈ U)
    (theoremIII1 : Set (Vec ℝ n) → ℝ → Set (Vec ℝ n)) (corollaryIV2 : Set (Vec ℝ n))
    (theoremIII2 : Set (Vec ℝ n) → Set (Vec ℝ n) → Set (Vec ℝ n)) (X₀ : Set (Vec ℝ n))
    {δ tf : ℝ} (hδ : 0 < δ) (htf : 0 < tf)
    (hIII1 : ∀ X t, 0 ≤ t → (exp (t • A) *ᵥ ·) '' X ⊆ theoremIII1 X t)
    (hIV2 : (LinearSys.canonical A : LinearSys ℝ n).inputReach (S := 𝒮) U δ
      ⊆ corollaryIV2)
    (hIII2 : ∀ X, ∀ t ∈ Set.Icc 0 δ, (exp (t • A) *ᵥ ·) '' X ⊆ theoremIII2 X (theoremIII1 X δ))
    {t : ℝ} (ht : t ∈ Set.Icc 0 tf) {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ X₀) {y : Vec ℝ n}
    (hy : y ∈ (LinearSys.canonical A : LinearSys ℝ n).inputReach (S := 𝒮) U t) : -- --- STMT ---
    exp (t • A) *ᵥ x₀ + y
      ∈ Krylov.alg2Corrected theoremIII1 corollaryIV2 theoremIII2 X₀ δ tf := by -- --- PROOF ---
  set Rp := (LinearSys.canonical A : LinearSys ℝ n).inputReach (S := 𝒮) U δ
    with hRp
  let box : Set (Vec ℝ n) → Set (Vec ℝ n) :=
    fun S => {x | ∀ i, ∃ y ∈ S, ∃ z ∈ S, y i ≤ x i ∧ x i ≤ z i}
  have hbox : ∀ S, S ⊆ box S := fun S x hx i => ⟨x, hx, x, hx, le_rfl, le_rfl⟩
  -- the listing's loop, restated
  let b : Set (Vec ℝ n) × Set (Vec ℝ n) × Set (Vec ℝ n) :=
    (theoremIII1 X₀ δ, box (convexHull ℝ (insert 0 corollaryIV2)),
      theoremIII2 X₀ (theoremIII1 X₀ δ) + box (convexHull ℝ (insert 0 corollaryIV2)))
  let F : ℕ → Set (Vec ℝ n) × Set (Vec ℝ n) × Set (Vec ℝ n)
      → Set (Vec ℝ n) × Set (Vec ℝ n) × Set (Vec ℝ n) := fun m prev =>
    (theoremIII1 X₀ (((m : ℝ) + 1 + 1) * δ),
      prev.2.1 + box (theoremIII1 corollaryIV2 (((m : ℝ) + 1) * δ)),
      theoremIII2 prev.1 (theoremIII1 prev.1 δ)
        + (prev.2.1 + box (theoremIII1 corollaryIV2 (((m : ℝ) + 1) * δ))))
  let st : ℕ → Set (Vec ℝ n) × Set (Vec ℝ n) × Set (Vec ℝ n) := fun m =>
    Nat.rec (motive := fun _ => Set (Vec ℝ n) × Set (Vec ℝ n) × Set (Vec ℝ n)) b F m
  show exp (t • A) *ᵥ x₀ + y ∈ ⋃ m ∈ Finset.range ⌈tf / δ⌉₊, (st m).2.2
  -- the pass for `m`: `R*_{h}`, the input part, and the step `[mδ, (m + 1)δ]`
  have key : ∀ m : ℕ, (exp ((((m : ℝ) + 1) * δ) • A) *ᵥ ·) '' X₀ ⊆ (st m).1
      ∧ ∑ i ∈ Finset.range (m + 1), (fun y => exp ((i * δ) • A) *ᵥ y) '' Rp ⊆ (st m).2.1
      ∧ ∀ s ∈ Set.Icc 0 δ, ∀ x ∈ X₀, ∀ z ∈ ∑ i ∈ Finset.range (m + 1),
          (fun y => exp ((i * δ) • A) *ᵥ y) '' Rp,
          exp ((m * δ + s) • A) *ᵥ x + z ∈ (st m).2.2 := by
    intro m
    induction m with
    | zero =>
      -- lines 1–5: `R_p(δ) ⊆ R*_{b,1} ⊆ box(conv(0ₙ, R*_{b,1}))`
      have hp : ∑ i ∈ Finset.range (0 + 1), (fun y => exp ((i * δ) • A) *ᵥ y) '' Rp
          ⊆ box (convexHull ℝ (insert 0 corollaryIV2)) := by
        rw [Finset.sum_range_one, Nat.cast_zero, zero_mul, zero_smul, exp_zero]
        simp only [one_mulVec, Set.image_id']
        exact hIV2.trans ((Set.subset_insert _ _).trans ((subset_convexHull ℝ _).trans
          (hbox _)))
      refine ⟨?_, hp, fun s hs x hx z hz => Set.add_mem_add ?_ (hp hz)⟩
      · rw [show (((0 : ℕ) : ℝ) + 1) * δ = δ by simp]
        exact hIII1 X₀ δ hδ.le
      · refine hIII2 X₀ s hs ⟨x, hx, ?_⟩
        simp
    | succ m ih =>
      -- lines 7–11: one more term `e^{A(m + 1)δ}R_p(δ) ⊆ box(R*_{b,m+2})`
      obtain ⟨ih1, ih2, -⟩ := ih
      have hp : ∑ i ∈ Finset.range (m + 1 + 1), (fun y => exp ((i * δ) • A) *ᵥ y) '' Rp
          ⊆ (st (m + 1)).2.1 := by
        rw [Finset.sum_range_succ]
        refine Set.add_subset_add ih2 ((Set.image_mono hIV2).trans ?_)
        refine (hIII1 _ _ (by positivity)).trans ((le_of_eq ?_).trans (hbox _))
        push_cast
        rfl
      refine ⟨?_, hp, fun s hs x hx z hz => Set.add_mem_add ?_ (hp hz)⟩
      · refine (le_of_eq ?_).trans (hIII1 X₀ _ (by positivity))
        push_cast
        rfl
      · -- `e^{A((m + 1)δ + s)}x = e^{As}e^{A(m + 1)δ}x`, from `R*_{h,m+1}`
        refine hIII2 (st m).1 s hs ⟨exp ((((m : ℝ) + 1) * δ) • A) *ᵥ x, ih1 ⟨x, hx, rfl⟩, ?_⟩
        show exp (s • A) *ᵥ _ = _
        rw [show ((m + 1 : ℕ) : ℝ) * δ + s = ((m : ℝ) + 1) * δ + s by push_cast; ring,
          Krylov.aux_exp_add_mulVec]
  obtain ⟨m, hm, s, hs, rfl⟩ := Krylov.aux_exists_step hδ htf ht
  have hy' := Krylov.inputReach_subset_sum_exp_image (LinearSys.canonical A : LinearSys ℝ n)
    (S := 𝒮) hbdd h0 hδ.le m hs.1 hs.2 hy
  simp only [Scalar.toRealMat_real] at hy'
  exact Set.mem_iUnion₂.2 ⟨m, Finset.mem_range.2 hm, (key m).2.2 s hs x₀ hx₀ y hy'⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
