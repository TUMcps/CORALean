module

public import CORALean.ContSet.Zonotope.Real.Theorems.ConstructEqConvexHullCorner
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Homeomorph.Lemmas
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# The largest cube in the lifted zonotope touches it low down

`[1, Lemma 6]`: for linearly independent `z₁, …, zₙ`, `Π = {x | |zᵢᵀx| ≤ 1}` (the reading its polar
needs; see `Zonotope.parallelotope_eq_abs_mulVec_le_counterexample`), `α = 1/(2n²R∞(Π))` and
`Z* = ∑ᵢ [0, 1](vᵢ + αe_{n+1})` over `vᵢ = ±zᵢ`, the largest cube `C` centered at `c = nαe_{n+1}`
inside `Z*` exists and has a vertex `q` on `∂Z*` with `qᵀe_{n+1} ∈ [0, α]`. The lift is
`Vec ℝ n × ℝ`, whose norm is the maximum norm, so `C` is a closed ball. Where the printed proof
bounds `r∞(Z*)` above, the argument needs it below: the cube of radius `(n - 1)α` fits, so the
lower vertices sit at height `nα - r∞(Z*) ∈ [0, α]`; an upper vertex on `∂Z*` mirrors through `c`
to a lower one, `Z*` being symmetric about `c`.

## Inputs
* `z` – linearly independent vectors
* `R` – largest norm
* `α` – lift height
* `Zs` – lifted polytope

## Hypotheses
* `hn` – dimension positive
* `hz` – vectors independent
* `hR` – `R` is the greatest norm
* `hα` – `α` defined from `R`
* `hZs` – `Zs` is the lifted zonotope

## Conclusion
* a largest cube exists with a vertex on the frontier

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Metric

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A box is the convex hull of its vertices, in `Vec ℝ n × ℝ` with the maximum norm. -/
theorem aux_lift_closedBall_subset_convexHull (c : Vec ℝ n × ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    closedBall c ρ ⊆ convexHull ℝ
      {q : Vec ℝ n × ℝ | (∀ i, |q.1 i - c.1 i| = ρ) ∧ |q.2 - c.2| = ρ} := by -- --- PROOF ---
  -- the horizontal part: the cube as the zonotope of the scaled unit vectors
  have h1 : closedBall c.1 ρ ⊆ convexHull ℝ {x : Vec ℝ n | ∀ i, |x i - c.1 i| = ρ} := by
    let Z : Zonotope (Vec ℝ n) := ⟨n, c.1, fun j => ρ • Pi.single j 1⟩
    intro x hx
    have hxZ : x ∈ Z.construct := by
      refine ⟨fun j => (x j - c.1 j) / ρ, fun j => ?_, ?_⟩
      · rw [abs_div, abs_of_pos hρ, div_le_one hρ, ← Real.dist_eq]
        exact (dist_le_pi_dist x c.1 j).trans (mem_closedBall.mp hx)
      · funext i
        simp [Z, Finset.sum_apply, Pi.single_apply, smul_smul]
        field_simp
        ring
    rw [Z.construct_eq_convexHull_corner] at hxZ
    refine convexHull_mono ?_ hxZ
    rintro _ ⟨σ, rfl⟩ i
    simp only [Zonotope.corner, Z, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      add_sub_cancel_left]
    split_ifs <;> simp [abs_of_pos hρ]
  -- the vertical part: an interval is the segment between its ends
  have h2 : closedBall c.2 ρ ⊆ convexHull ℝ {t : ℝ | |t - c.2| = ρ} := by
    intro t ht
    rw [Real.closedBall_eq_Icc, ← segment_eq_Icc (by linarith), ← convexHull_pair] at ht
    refine convexHull_mono ?_ ht
    rintro _ (rfl | rfl) <;> simp [abs_of_pos hρ]
  intro q hq
  rw [← closedBall_prod_same] at hq
  have hprod := convexHull_prod (R := ℝ) {x : Vec ℝ n | ∀ i, |x i - c.1 i| = ρ}
    {t : ℝ | |t - c.2| = ρ}
  have hmem : q ∈ convexHull ℝ ({x : Vec ℝ n | ∀ i, |x i - c.1 i| = ρ} ×ˢ
      {t : ℝ | |t - c.2| = ρ}) := by
    rw [hprod]; exact ⟨h1 hq.1, h2 hq.2⟩
  refine convexHull_mono ?_ hmem
  rintro p ⟨hp1, hp2⟩
  exact ⟨hp1, hp2⟩

/-- The points of `Z*`, the image of the box `[0, 1]^{2n}` of weights. -/
theorem aux_lift_eq_image (w : Fin n ⊕ Fin n → Vec ℝ n × ℝ) :
    {p | ∃ μ : Fin n ⊕ Fin n → ℝ, (∀ k, 0 ≤ μ k ∧ μ k ≤ 1) ∧ p = ∑ k, μ k • w k}
      = (fun μ : Fin n ⊕ Fin n → ℝ => ∑ k, μ k • w k) ''
          Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1) := by
  ext p
  constructor
  · rintro ⟨μ, hμ, rfl⟩; exact ⟨μ, fun k _ => hμ k, rfl⟩
  · rintro ⟨μ, hμ, rfl⟩; exact ⟨μ, fun k => hμ k (Set.mem_univ k), rfl⟩

/-- `Z*` is compact, hence closed. -/
theorem aux_lift_isClosed (w : Fin n ⊕ Fin n → Vec ℝ n × ℝ) :
    IsClosed {p | ∃ μ : Fin n ⊕ Fin n → ℝ, (∀ k, 0 ≤ μ k ∧ μ k ≤ 1) ∧ p = ∑ k, μ k • w k} := by
  rw [aux_lift_eq_image]
  refine ((isCompact_univ_pi fun _ => isCompact_Icc).image ?_).isClosed
  exact continuous_finsetSum _ fun k _ => (continuous_apply k).smul continuous_const

/-- `Z*` is convex. -/
theorem aux_lift_convex (w : Fin n ⊕ Fin n → Vec ℝ n × ℝ) :
    Convex ℝ {p | ∃ μ : Fin n ⊕ Fin n → ℝ, (∀ k, 0 ≤ μ k ∧ μ k ≤ 1) ∧
      p = ∑ k, μ k • w k} := by -- --- PROOF ---
  rw [aux_lift_eq_image]
  let f : (Fin n ⊕ Fin n → ℝ) →ₗ[ℝ] Vec ℝ n × ℝ :=
    { toFun := fun μ => ∑ k, μ k • w k
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a b => by simp [Finset.smul_sum, smul_smul] }
  exact (convex_pi fun _ _ => convex_Icc 0 1).linear_image f

/-- For `‖s‖ ≤ (n - 1)α`, the coefficients `s = ∑ aᵢzᵢ` have `∑|aᵢ| ≤ 1/2`: `∑|aᵢ| = sᵀx` for
the `x ∈ Π` with `zᵢᵀx = sign aᵢ`, and `sᵀx ≤ n‖s‖‖x‖ ≤ n(n - 1)αR∞(Π)`. -/
theorem aux_lift_exists_coeff (hn : 1 ≤ n) (z : Fin n → Vec ℝ n) (hz : LinearIndependent ℝ z)
    {R : ℝ} (hR : IsGreatest ((fun x => ‖x‖) '' {x : Vec ℝ n | ∀ i, |z i ⬝ᵥ x| ≤ 1}) R)
    (hRpos : 0 < R) {s : Vec ℝ n} (hs : ‖s‖ ≤ (n - 1) * (1 / (2 * n ^ 2 * R))) :
    ∃ a : Fin n → ℝ, ∑ i, a i • z i = s ∧ ∑ i, |a i| ≤ 1 / 2 := by -- --- PROOF ---
  -- the coefficients `a = sᵀM⁻¹` of `s` in the basis `zᵢ`, `M` the matrix of rows `zᵢ`
  let M : Mat ℝ n n := Matrix.of fun i j => z i j
  have hM : IsUnit M := (Matrix.linearIndependent_rows_iff_isUnit).mp hz
  have hMdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM
  let a : Fin n → ℝ := s ᵥ* M⁻¹
  have hvec : ∀ b : Fin n → ℝ, ∑ i, b i • z i = b ᵥ* M := fun b => by
    funext j; simp [vecMul, dotProduct, M, Finset.sum_apply, mul_comm]
  have ha : ∑ i, a i • z i = s := by
    rw [hvec, vecMul_vecMul, nonsing_inv_mul _ hMdet, vecMul_one]
  refine ⟨a, ha, ?_⟩
  -- the point of `Π` that the signs of `a` pick out
  let ε : Fin n → ℝ := fun i => if 0 ≤ a i then 1 else -1
  let x : Vec ℝ n := M⁻¹ *ᵥ ε
  have hMx : M *ᵥ x = ε := by rw [mulVec_mulVec, mul_nonsing_inv _ hMdet, one_mulVec]
  have hzx : ∀ i, z i ⬝ᵥ x = ε i := fun i => by
    rw [← hMx]; rfl
  have hxP : x ∈ {x : Vec ℝ n | ∀ i, |z i ⬝ᵥ x| ≤ 1} := fun i => by
    rw [hzx]; simp only [ε]; split_ifs <;> simp
  have hxR : ‖x‖ ≤ R := hR.2 ⟨x, hxP, rfl⟩
  -- `∑ |aᵢ| = ∑ aᵢ zᵢᵀx = sᵀx`
  have hsum : ∑ i, |a i| = s ⬝ᵥ x := by
    rw [← ha]
    simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ∑ j, a i * z i j * x j = a i * (z i ⬝ᵥ x) by
      simp [dotProduct, Finset.mul_sum, mul_assoc], hzx]
    simp only [ε]; split_ifs with h
    · rw [mul_one, abs_of_nonneg h]
    · rw [mul_neg_one, abs_of_neg (not_le.mp h)]
  -- `sᵀx ≤ n‖s‖‖x‖`, coordinate by coordinate
  have hdot : s ⬝ᵥ x ≤ n * (‖s‖ * ‖x‖) := by
    have h : ∀ j, s j * x j ≤ ‖s‖ * ‖x‖ := fun j => by
      have hs' : |s j| ≤ ‖s‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm s j
      have hx' : |x j| ≤ ‖x‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm x j
      calc s j * x j ≤ |s j * x j| := le_abs_self _
        _ = |s j| * |x j| := abs_mul _ _
        _ ≤ ‖s‖ * ‖x‖ := mul_le_mul hs' hx' (abs_nonneg _) (norm_nonneg _)
    calc s ⬝ᵥ x = ∑ j, s j * x j := rfl
      _ ≤ ∑ _j : Fin n, ‖s‖ * ‖x‖ := Finset.sum_le_sum fun j _ => h j
      _ = n * (‖s‖ * ‖x‖) := by simp
  -- `n‖s‖‖x‖ ≤ n(n - 1)αR = (n - 1)/(2n) ≤ 1/2`
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbound : (n : ℝ) * (‖s‖ * ‖x‖) ≤ n * ((n - 1) * (1 / (2 * n ^ 2 * R)) * R) := by
    have h0 : 0 ≤ ‖s‖ * ‖x‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have h1 : ‖s‖ * ‖x‖ ≤ (n - 1) * (1 / (2 * n ^ 2 * R)) * R :=
      mul_le_mul hs hxR (norm_nonneg _) (by have : (0:ℝ) ≤ n - 1 := by linarith
                                            positivity)
    exact mul_le_mul_of_nonneg_left h1 (by linarith)
  have heq : (n : ℝ) * ((n - 1) * (1 / (2 * n ^ 2 * R)) * R) = (n - 1) / (2 * n) := by
    field_simp
  have hhalf : ((n : ℝ) - 1) / (2 * n) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  rw [hsum]
  linarith

/-- The cube of radius `(n - 1)α` around `c` lies in `Z*`: weights with difference `aᵢ` on the
pair `±zᵢ` and total `t/α ∈ [1, 2n - 1]`. -/
theorem aux_cube_subset_lift (hn : 1 ≤ n) (z : Fin n → Vec ℝ n) (hz : LinearIndependent ℝ z)
    {R : ℝ} (hR : IsGreatest ((fun x => ‖x‖) '' {x : Vec ℝ n | ∀ i, |z i ⬝ᵥ x| ≤ 1}) R)
    (hRpos : 0 < R) : -- --- CONCL ---
    closedBall (((0 : Vec ℝ n), (n : ℝ) * (1 / (2 * n ^ 2 * R))) : Vec ℝ n × ℝ)
        ((n - 1) * (1 / (2 * n ^ 2 * R))) ⊆
      {p | ∃ μ : Fin n ⊕ Fin n → ℝ, (∀ k, 0 ≤ μ k ∧ μ k ≤ 1) ∧
        p = ∑ k, μ k • ((Sum.elim z (fun i => -z i) k, 1 / (2 * n ^ 2 * R)) :
          Vec ℝ n × ℝ)} := by -- --- PROOF ---
  set α : ℝ := 1 / (2 * n ^ 2 * R) with hαdef
  have hα : 0 < α := by positivity
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  -- `s` has coefficients `aᵢ` with `A = ∑ |aᵢ| ≤ 1/2`
  rintro ⟨s, t⟩ hp
  rw [mem_closedBall, Prod.dist_eq, max_le_iff, dist_zero_right, Real.dist_eq] at hp
  dsimp only at hp
  obtain ⟨a, ha, hA⟩ := aux_lift_exists_coeff hn z hz hR hRpos hp.1
  set A : ℝ := ∑ i, |a i| with hAdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hai : ∀ i, |a i| ≤ 1 / 2 := fun i =>
    (Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)).trans hA
  -- the total weight `T = t/α`, spread over the pairs by `θ`
  set T : ℝ := t / α with hTdef
  have hT1 : 1 ≤ T := by
    rw [hTdef, le_div_iff₀ hα]; have := (abs_le.mp hp.2).1; nlinarith
  have hT2 : T ≤ 2 * n - 1 := by
    rw [hTdef, div_le_iff₀ hα]; have := (abs_le.mp hp.2).2; nlinarith
  have hden : 0 < 2 * (n : ℝ) - 2 * A := by linarith
  set θ : ℝ := (T - A) / (2 * n - 2 * A) with hθdef
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hden.le
  have hθ1 : θ ≤ 1 := by rw [hθdef, div_le_one hden]; linarith
  -- the pair `±zᵢ` gets total weight `σᵢ ∈ [|aᵢ|, 2 - |aᵢ|]`, split to differ by `aᵢ`
  let σ : Fin n → ℝ := fun i => |a i| + θ * (2 - 2 * |a i|)
  let μ : Fin n ⊕ Fin n → ℝ := Sum.elim (fun i => (σ i + a i) / 2) (fun i => (σ i - a i) / 2)
  have hσb : ∀ i, 0 ≤ σ i - |a i| ∧ σ i + |a i| ≤ 2 := fun i => by
    have h0 := abs_nonneg (a i)
    have h1 := hai i
    constructor
    · simp only [σ]; nlinarith
    · simp only [σ]; nlinarith
  have hσT : θ * (2 * n - 2 * A) = T - A := by
    rw [hθdef, div_mul_cancel₀ _ hden.ne']
  have hσ : ∑ i, σ i = T := by
    have h : ∑ i, σ i = A + θ * (2 * n - 2 * A) := by
      simp only [σ, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hAdef]
      ring
    rw [h, hσT]; ring
  -- every weight is in `[0, 1]`
  refine ⟨μ, ?_, ?_⟩
  · have hle := fun i => abs_le.mp (le_refl |a i|)
    rintro (i | i)
    · simp only [μ, Sum.elim_inl]
      constructor <;> linarith [hσb i, hle i, neg_abs_le (a i), le_abs_self (a i)]
    · simp only [μ, Sum.elim_inr]
      constructor <;> linarith [hσb i, hle i, neg_abs_le (a i), le_abs_self (a i)]
  · -- the two coordinates: `∑ aᵢzᵢ = s` and `α ∑ σᵢ = αT = t`
    rw [Fintype.sum_sum_type, Prod.ext_iff]
    simp only [μ, Sum.elim_inl, Sum.elim_inr, Prod.fst_add, Prod.snd_add, Prod.fst_sum,
      Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_neg, Finset.sum_neg_distrib]
    constructor
    · rw [← ha, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_smul]; congr 1; ring
    · rw [← Finset.sum_add_distrib]
      rw [show ∑ i, ((σ i + a i) / 2 * α + (σ i - a i) / 2 * α) = α * ∑ i, σ i by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, hσ, hTdef]
      field_simp


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[1, Lemma 6]`: the largest cube `C` centered at `c = (0, nα)` inside `Z*` exists, and some
vertex `q` of `C` lies on `∂Z*` with `qᵀe_{n+1} ∈ [0, α]`. -/
theorem exists_cube_vertex_mem_frontier_lift (hn : 1 ≤ n) (z : Fin n → Vec ℝ n)
    (hz : LinearIndependent ℝ z) {R : ℝ}
    (hR : IsGreatest ((fun x => ‖x‖) '' {x : Vec ℝ n | ∀ i, |z i ⬝ᵥ x| ≤ 1}) R)
    {α : ℝ} (hα : α = 1 / (2 * n ^ 2 * R)) {Zs : Set (Vec ℝ n × ℝ)}
    (hZs : Zs = {p | ∃ μ : Fin n ⊕ Fin n → ℝ, (∀ k, 0 ≤ μ k ∧ μ k ≤ 1) ∧
      p = ∑ k, μ k • ((Sum.elim z (fun i => -z i) k, α) : Vec ℝ n × ℝ)}) : -- --- CONCL ---
    ∃ r, IsGreatest {r | closedBall (((0 : Vec ℝ n), (n : ℝ) * α) : Vec ℝ n × ℝ) r ⊆ Zs} r ∧
      ∃ q ∈ frontier Zs, (∀ i, |q.1 i| = r) ∧ |q.2 - n * α| = r ∧
        q.2 ∈ Set.Icc 0 α := by -- --- PROOF ---
  -- `R > 0`: a small multiple of a unit vector lies in `Π`
  have hR0 : 0 < R := by
    let i₀ : Fin n := ⟨0, hn⟩
    let e : Vec ℝ n := Pi.single i₀ 1
    set K : ℝ := 1 + ∑ i, |z i ⬝ᵥ e| with hKdef
    have hK : 0 < K :=
      add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => abs_nonneg _)
    have hmem : K⁻¹ • e ∈ {x : Vec ℝ n | ∀ i, |z i ⬝ᵥ x| ≤ 1} := fun i => by
      rw [dotProduct_smul, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hK, inv_mul_le_iff₀ hK]
      have := Finset.single_le_sum (fun j _ => abs_nonneg (z j ⬝ᵥ e)) (Finset.mem_univ i)
      linarith
    have hle : ‖K⁻¹ • e‖ ≤ R := hR.2 ⟨_, hmem, rfl⟩
    have hco : |(K⁻¹ • e) i₀| ≤ ‖K⁻¹ • e‖ := by
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ i₀
    have hval : (K⁻¹ • e) i₀ = K⁻¹ := by simp [e]
    rw [hval, abs_of_pos (inv_pos.mpr hK)] at hco
    linarith [inv_pos.mpr hK]
  -- `Z*`, `c` and `α` named
  subst hα hZs
  set α : ℝ := 1 / (2 * n ^ 2 * R) with hαdef
  have hα0 : 0 < α := by positivity
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set w : Fin n ⊕ Fin n → Vec ℝ n × ℝ := fun k => (Sum.elim z (fun i => -z i) k, α) with hwdef
  set Zs := {p | ∃ μ : Fin n ⊕ Fin n → ℝ, (∀ k, 0 ≤ μ k ∧ μ k ≤ 1) ∧ p = ∑ k, μ k • w k}
    with hZsdef
  set c : Vec ℝ n × ℝ := ((0 : Vec ℝ n), (n : ℝ) * α) with hcdef
  have hclosed : IsClosed Zs := aux_lift_isClosed w
  have hconv : Convex ℝ Zs := aux_lift_convex w
  -- every point of `Z*` sits at a height in `[0, 2nα]`
  have hheight : ∀ p ∈ Zs, 0 ≤ p.2 ∧ p.2 ≤ 2 * n * α := by
    rintro _ ⟨μ, hμ, rfl⟩
    rw [Prod.snd_sum]
    simp only [Prod.smul_snd, smul_eq_mul, w]
    constructor
    · exact Finset.sum_nonneg fun k _ => mul_nonneg (hμ k).1 hα0.le
    · calc ∑ k, μ k * α ≤ ∑ _k : Fin n ⊕ Fin n, α :=
            Finset.sum_le_sum fun k _ => by nlinarith [(hμ k).2]
        _ = 2 * n * α := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  -- `Z*` is symmetric about `c`: the weights `1 - μ`
  have hsum_w : ∑ k, w k = c + c := by
    rw [Fintype.sum_sum_type, Prod.ext_iff]
    simp only [w, Sum.elim_inl, Sum.elim_inr, Prod.fst_add, Prod.snd_add, Prod.fst_sum,
      Prod.snd_sum, Finset.sum_neg_distrib, add_neg_cancel, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, c]
    constructor
    · simp
    · simp
  have hsymm : ∀ p ∈ Zs, (c + c) - p ∈ Zs := by
    rintro _ ⟨μ, hμ, rfl⟩
    refine ⟨fun k => 1 - μ k, fun k => ⟨by linarith [(hμ k).2], by linarith [(hμ k).1]⟩, ?_⟩
    simp only [sub_smul, one_smul, Finset.sum_sub_distrib, hsum_w]
  -- the radii `r` with the cube `C` of radius `r` inside `Z*`
  set S : Set ℝ := {r | closedBall c r ⊆ Zs} with hSdef
  have hρS : ((n : ℝ) - 1) * α ∈ S := aux_cube_subset_lift hn z hz hR hR0
  -- `C` reaches down to height `nα - r`, which must be `≥ 0`
  have hSbdd : ∀ r ∈ S, r ≤ n * α := by
    intro r hr
    by_cases hneg : r < 0
    · have : (0 : ℝ) ≤ n * α := by positivity
      linarith
    have hpt : (((0 : Vec ℝ n), (n : ℝ) * α - r) : Vec ℝ n × ℝ) ∈ closedBall c r := by
      rw [mem_closedBall, Prod.dist_eq, max_le_iff]
      refine ⟨by simp [c]; linarith, ?_⟩
      rw [Real.dist_eq]; simp only [c]
      rw [show (n : ℝ) * α - r - n * α = -r by ring, abs_neg, abs_of_nonneg (not_lt.mp hneg)]
    have := (hheight _ (hr hpt)).1
    simp only at this
    linarith
  -- `r = sup S`, between `(n - 1)α` and `nα`
  have hbdd : BddAbove S := ⟨n * α, hSbdd⟩
  have hne : S.Nonempty := ⟨_, hρS⟩
  set r := sSup S with hrdef
  have hr_ge : ((n : ℝ) - 1) * α ≤ r := le_csSup hbdd hρS
  have hr_le : r ≤ n * α := csSup_le hne hSbdd
  have hr0 : 0 ≤ r := le_trans (mul_nonneg (by linarith) hα0.le) hr_ge
  -- the supremum is attained: the open cube lies in `Z*`, and `Z*` is closed
  have hrS : r ∈ S := by
    have hball : ball c r ⊆ Zs := fun y hy => by
      obtain ⟨r', hr'S, hr'⟩ := exists_lt_of_lt_csSup hne (mem_ball.mp hy)
      exact hr'S (mem_closedBall.mpr hr'.le)
    rcases hr0.lt_or_eq with hrpos | hr00
    · intro y hy
      rw [← closure_ball c hrpos.ne'] at hy
      exact (closure_minimal hball hclosed) hy
    · intro y hy
      rw [← hr00, closedBall_zero, Set.mem_singleton_iff] at hy
      rw [hy]
      exact hρS (mem_closedBall_self (mul_nonneg (by linarith) hα0.le))
  have hgreat : IsGreatest S r := ⟨hrS, fun r' hr' => le_csSup hbdd hr'⟩
  refine ⟨r, hgreat, ?_⟩
  -- the vertices of `C`
  set K : Set (Vec ℝ n × ℝ) := {q | (∀ i, |q.1 i - c.1 i| = r) ∧ |q.2 - c.2| = r} with hKdef
  have hKball : K ⊆ closedBall c r := fun q hq => by
    rw [mem_closedBall, Prod.dist_eq, max_le_iff]
    refine ⟨(dist_pi_le_iff hr0).mpr fun i => ?_, ?_⟩
    · rw [Real.dist_eq]; exact (hq.1 i).le
    · rw [Real.dist_eq]; exact hq.2.le
  -- the vertices form a compact set
  have hKclosed : IsClosed K := by
    have hK : K = (⋂ i, {q : Vec ℝ n × ℝ | |q.1 i - c.1 i| = r}) ∩ {q | |q.2 - c.2| = r} := by
      ext q; simp [K]
    rw [hK]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const)
      (isClosed_eq (by fun_prop) continuous_const)
  -- some vertex is on `∂Z*`: otherwise a slightly larger cube still fits
  have hfront : ∃ q ∈ K, q ∈ frontier Zs := by
    by_contra hno
    simp only [not_exists, not_and] at hno
    have hKint : K ⊆ interior Zs := fun q hq => by
      by_contra hqi
      exact hno q hq ⟨subset_closure (hrS (hKball hq)), hqi⟩
    -- all vertices interior: a whole `δ`-neighbourhood of them is in `Z*`
    have hKc : IsCompact K := (isCompact_closedBall c r).of_isClosed_subset hKclosed hKball
    obtain ⟨δ, hδ, hthick⟩ := hKc.exists_thickening_subset_open isOpen_interior hKint
    have hpos : 0 < r + δ / 2 := by linarith
    have hbig : r + δ / 2 ∈ S := by
      intro y hy
      refine (convexHull_min ?_ hconv) (aux_lift_closedBall_subset_convexHull c hpos hy)
      intro q' hq'
      -- the vertex of `C` on the ray from `c` through `q'`, within `δ/2` of it
      set l : ℝ := r / (r + δ / 2) with hldef
      have hl0 : 0 ≤ l := div_nonneg hr0 hpos.le
      have hl1 : l * (r + δ / 2) = r := div_mul_cancel₀ _ hpos.ne'
      set q : Vec ℝ n × ℝ := c + l • (q' - c) with hqdef
      -- each coordinate of `q - c` is `l(r + δ/2) = r`
      have hqK : q ∈ K := by
        refine ⟨fun i => ?_, ?_⟩
        · simp only [q, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, Pi.add_apply, Pi.smul_apply,
            Pi.sub_apply, smul_eq_mul, add_sub_cancel_left, abs_mul, abs_of_nonneg hl0, hq'.1 i,
            hl1]
        · simp only [q, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul,
            add_sub_cancel_left, abs_mul, abs_of_nonneg hl0, hq'.2, hl1]
      -- `q' - q = (1 - l)(q' - c)`, of norm `δ/2`
      have hdist : dist q' q < δ := by
        have hle : dist q' q ≤ δ / 2 := by
          have hfac : (1 - l) * (r + δ / 2) = δ / 2 := by rw [sub_mul, hl1]; ring
          have h1l : 0 ≤ 1 - l := by
            rw [sub_nonneg, hldef, div_le_one hpos]; linarith
          -- coordinate by coordinate
          rw [Prod.dist_eq, max_le_iff]
          refine ⟨(dist_pi_le_iff (by linarith)).mpr fun i => ?_, ?_⟩
          · rw [Real.dist_eq]
            simp only [q, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, Pi.add_apply,
              Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
            rw [show q'.1 i - (c.1 i + l * (q'.1 i - c.1 i)) = (1 - l) * (q'.1 i - c.1 i) by ring,
              abs_mul, abs_of_nonneg h1l, hq'.1 i, hfac]
          · rw [Real.dist_eq]
            simp only [q, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
            rw [show q'.2 - (c.2 + l * (q'.2 - c.2)) = (1 - l) * (q'.2 - c.2) by ring,
              abs_mul, abs_of_nonneg h1l, hq'.2, hfac]
        linarith
      exact interior_subset (hthick (mem_thickening_iff.mpr ⟨q, hqK, hdist⟩))
    have := hgreat.2 hbig
    linarith
  obtain ⟨q, hqK, hqF⟩ := hfront
  have hc1 : ∀ i, c.1 i = 0 := fun i => rfl
  have hc2 : c.2 = n * α := rfl
  -- a lower vertex is the one wanted; an upper one mirrors through `c` to a lower one
  rcases abs_eq hr0 |>.mp hqK.2 with hup | hdown
  · let φ := Homeomorph.subLeft (c + c)
    have hφZ : φ '' Zs = Zs := by
      ext y
      constructor
      · rintro ⟨p, hp, rfl⟩; exact hsymm p hp
      · intro hy; exact ⟨(c + c) - y, hsymm y hy, sub_sub_cancel _ _⟩
    -- `x ↦ 2c - x` maps `Z*` onto itself, hence its frontier too
    have hq'F : (c + c) - q ∈ frontier Zs := by
      rw [← hφZ, ← φ.image_frontier]; exact ⟨q, hqF, rfl⟩
    refine ⟨(c + c) - q, hq'F, fun i => ?_, ?_, ?_⟩
    · have := hqK.1 i
      simp only [hc1, sub_zero] at this
      simp only [Prod.fst_sub, Prod.fst_add, Pi.sub_apply, Pi.add_apply, hc1, zero_add,
        zero_sub, abs_neg, this]
    · simp only [Prod.snd_sub, Prod.snd_add, hc2]
      rw [show n * α + n * α - q.2 - n * α = -(q.2 - c.2) by rw [hc2]; ring, abs_neg, hup,
        abs_of_nonneg hr0]
    · simp only [Prod.snd_sub, Prod.snd_add, hc2]
      constructor <;> linarith [show q.2 = n * α + r by linarith [hc2]]
  · refine ⟨q, hqF, fun i => ?_, ?_, ?_⟩
    · have := hqK.1 i
      simpa [hc1] using this
    · rw [← hc2]; exact hqK.2
    · constructor <;> linarith [show q.2 = n * α - r by linarith [hc2]]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
