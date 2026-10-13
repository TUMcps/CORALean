import CORALean.ContSet.Zonotope.Real.Operations.GoffinSeparator
import CORALean.ContSet.Zonotope.Real.Theorems.Convex
import CORALean.ContSet.Zonotope.Real.Theorems.IsFullDimIff
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.Normed.Group.Pointwise
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Goffin's separator separates

[1, Sec. 4.5]: for a full-dimensional zonotope `Z` centred at `0` and `x₀ ∉ Z`, with `β*` the
largest `β` with `βx₀ ∈ Z` (Step 1) and `H = (h₁, …, h_{n-1})` a basis of a facet `F` through
`x* = β*x₀` (Steps 2 and 3, from Cor. 3.5 and Thm. 3.3(d)), the output `a` of Step 4 and
`b = aᵀx*` satisfy `Z ⊆ {aᵀx ≤ b}`, `aᵀx₀ > b` and `{aᵀx = b} ∩ Z = F`. The facet is
`F = {x ∈ Z | wᵀx = max_Z wᵀ}` for a normal `w ≠ 0`, its basis linearly independent in the
direction space of its affine hull. `a` is orthogonal to the `n - 1` independent `hᵢ`, as `w` is,
so `a = κw` with `κ = x₀ᵀw/wᵀw`; `κ > 0` because `0` is interior (full dimension, central
symmetry), and `β* < 1` because `Z` is convex and `x₀ ∉ Z`.

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A vector orthogonal to every member of a family is orthogonal to its span. -/
theorem Zonotope.aux_dot_eq_zero_of_mem_span {ι : Type} (v : Vec ℝ (k + 1))
    (b : ι → Vec ℝ (k + 1)) (hb : ∀ i, v ⬝ᵥ b i = 0) {x : Vec ℝ (k + 1)}
    (hx : x ∈ Submodule.span ℝ (Set.range b)) : v ⬝ᵥ x = 0 := by -- --- PROOF ---
  let φ : Vec ℝ (k + 1) →ₗ[ℝ] ℝ :=
    { toFun := fun y => v ⬝ᵥ y
      map_add' := dotProduct_add v
      map_smul' := fun c y => dotProduct_smul c v y }
  have hle : Submodule.span ℝ (Set.range b) ≤ LinearMap.ker φ :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb i)
  exact hle hx

/-- `0 < xᵀx` for `x ≠ 0`. -/
theorem Zonotope.aux_dot_self_pos {x : Vec ℝ (k + 1)} (hx : x ≠ 0) : 0 < x ⬝ᵥ x := by
  have h0 : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  rcases h0.lt_or_eq with h | h
  · exact h
  · exact absurd (dotProduct_self_eq_zero.1 h.symm) hx


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.5]: `Z ⊆ {aᵀx ≤ b}`, `aᵀx₀ > b`, and `{aᵀx = b} ∩ Z` is the facet `F`. -/
theorem Zonotope.goffinSeparator_spec (Z : Zonotope (Vec ℝ (k + 1))) (hc : Z.c = 0)
    (hfull : Submodule.span ℝ (Set.range Z.G) = ⊤) {x₀ : Vec ℝ (k + 1)} (hx₀ : x₀ ∉ Z.construct)
    {βstar : ℝ} (hβ : IsGreatest {β | β • x₀ ∈ Z.construct} βstar)
    (w : Vec ℝ (k + 1)) (hw : w ≠ 0) (hmax : ∀ y ∈ Z.construct, w ⬝ᵥ y ≤ w ⬝ᵥ (βstar • x₀))
    (H : Mat ℝ (k + 1) k) (hH : LinearIndependent ℝ fun i => Hᵀ i)
    (hHF : ∀ i, Hᵀ i ∈ vectorSpan ℝ
      {x | x ∈ Z.construct ∧ ∀ y ∈ Z.construct, w ⬝ᵥ y ≤ w ⬝ᵥ x}) :
    let s := Zonotope.goffinSeparator βstar x₀ H
    Z.construct ⊆ {x | s.1 ⬝ᵥ x ≤ s.2} ∧ s.2 < s.1 ⬝ᵥ x₀ ∧
      {x | x ∈ Z.construct ∧ s.1 ⬝ᵥ x = s.2}
        = {x | x ∈ Z.construct ∧ ∀ y ∈ Z.construct, w ⬝ᵥ y ≤ w ⬝ᵥ x} := by -- --- PROOF ---
  intro s
  set a := (1 - H * (Hᵀ * H)⁻¹ * Hᵀ) *ᵥ x₀ with ha
  set F := {x | x ∈ Z.construct ∧ ∀ y ∈ Z.construct, w ⬝ᵥ y ≤ w ⬝ᵥ x} with hF
  have hs : s = (a, a ⬝ᵥ (βstar • x₀)) := rfl
  -- `0` is interior: a point of the interior, its reflection, and their midpoint
  have hneg : -Z.construct = Z.construct := by
    ext x
    constructor
    · rintro ⟨β, hβ1, hx⟩
      refine ⟨-β, fun j => by simpa using hβ1 j, ?_⟩
      rw [hc, zero_add] at hx ⊢
      rw [← neg_neg x, hx]
      simp [Finset.sum_neg_distrib]
    · rintro ⟨β, hβ1, rfl⟩
      refine ⟨-β, fun j => by simpa using hβ1 j, ?_⟩
      simp [hc, Finset.sum_neg_distrib]
  have hint0 : (0 : Vec ℝ (k + 1)) ∈ interior Z.construct := by
    -- `-y` is interior with `y`, `Z` being symmetric
    obtain ⟨y, hy⟩ := (Zonotope.isFullDim_iff Z).2 hfull
    have hy' : -y ∈ interior Z.construct := by
      have himg := (Homeomorph.neg (Vec ℝ (k + 1))).image_interior Z.construct
      have hmem : -y ∈ (Homeomorph.neg (Vec ℝ (k + 1))) '' interior Z.construct := ⟨y, hy, rfl⟩
      rw [himg] at hmem
      simpa [Set.image_neg_eq_neg, hneg] using hmem
    have h := (Zonotope.convex_construct Z).interior hy hy' (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa [← smul_add] using h
  -- a ball around `0` in `Z`, so a small enough multiple of any vector is in `Z`
  have h0Z : (0 : Vec ℝ (k + 1)) ∈ Z.construct := interior_subset hint0
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint0)
  have hsmall : ∀ v : Vec ℝ (k + 1), (ε / (2 * (‖v‖ + 1))) • v ∈ Z.construct := by
    intro v
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg v]
  -- `w` is orthogonal to the direction space of `F`, so to every `hᵢ`
  have hwF : ∀ v ∈ vectorSpan ℝ F, w ⬝ᵥ v = 0 := by
    intro v hv
    rw [vectorSpan_def] at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, hp, q, hq, rfl⟩ := hx
      have h1 := hp.2 q hq.1
      have h2 := hq.2 p hp.1
      show w ⬝ᵥ (p -ᵥ q) = 0
      rw [vsub_eq_sub, dotProduct_sub]
      linarith
    | zero => simp
    | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
    | smul c x _ hx => rw [dotProduct_smul, hx, smul_zero]
  have hwH : ∀ i, w ⬝ᵥ Hᵀ i = 0 := fun i => hwF _ (hHF i)
  have hHw : Hᵀ *ᵥ w = 0 := funext fun i => by
    rw [Pi.zero_apply, ← hwH i, dotProduct_comm]
    rfl
  -- `HᵀH` is invertible: `HᵀHv = 0` gives `‖Hv‖² = 0`, and the columns are independent
  have hdet : IsUnit (Hᵀ * H).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv, hHv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hvv : (H *ᵥ v) ⬝ᵥ (H *ᵥ v) = 0 := by
      have h := congrArg (fun z => v ⬝ᵥ z) hHv
      simp only [dotProduct_zero, ← mulVec_mulVec, mulVec_transpose] at h
      rw [dotProduct_mulVec, dotProduct_comm]
      exact h
    have hHv0 : H *ᵥ v = 0 := dotProduct_self_eq_zero.1 hvv
    have hsum : ∑ i, v i • Hᵀ i = 0 := by
      rw [← hHv0]
      funext j
      simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
    exact hv (funext fun i => Fintype.linearIndependent_iff.1 hH v hsum i)
  -- `a ⟂ hᵢ`, since `Hᵀ(I - H(HᵀH)⁻¹Hᵀ) = 0`
  have hHa : Hᵀ *ᵥ a = 0 := by
    rw [ha, mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul, sub_self, zero_mulVec]
  have haH : ∀ i, a ⬝ᵥ Hᵀ i = 0 := fun i => by
    rw [dotProduct_comm, ← Pi.zero_apply (M := fun _ => ℝ) i, ← hHa]
    rfl
  have haw : a ⬝ᵥ w = x₀ ⬝ᵥ w := by
    rw [ha, sub_mulVec, one_mulVec, sub_dotProduct, ← mulVec_mulVec, ← mulVec_mulVec,
      dotProduct_comm (H *ᵥ _), dotProduct_mulVec, ← mulVec_transpose, hHw, zero_dotProduct,
      sub_zero]
  -- the `hᵢ` and `w` span the space, so `a`, orthogonal to the `hᵢ`, is a multiple of `w`
  have hww : 0 < w ⬝ᵥ w := Zonotope.aux_dot_self_pos hw
  let b : Option (Fin k) → Vec ℝ (k + 1) := fun o => o.elim w fun i => Hᵀ i
  have hwspan : w ∉ Submodule.span ℝ (Set.range fun i => Hᵀ i) := fun hmem =>
    (ne_of_gt hww) (Zonotope.aux_dot_eq_zero_of_mem_span w _ hwH hmem)
  have hlin : LinearIndependent ℝ b := linearIndependent_option.2 ⟨hH, hwspan⟩
  have hspan : Submodule.span ℝ (Set.range b) = ⊤ :=
    hlin.span_eq_top_of_card_eq_finrank (by simp)
  set κ := (a ⬝ᵥ w) / (w ⬝ᵥ w) with hκdef
  have haκ : a = κ • w := by
    have hvb : ∀ o, (a - κ • w) ⬝ᵥ b o = 0 := by
      rintro (_ | i)
      · show (a - κ • w) ⬝ᵥ w = 0
        rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, hκdef, div_mul_cancel₀ _ hww.ne',
          sub_self]
      · show (a - κ • w) ⬝ᵥ Hᵀ i = 0
        rw [sub_dotProduct, smul_dotProduct, haH, hwH, smul_zero, sub_zero]
    have h0 := Zonotope.aux_dot_eq_zero_of_mem_span (a - κ • w) b hvb
      (hspan ▸ Submodule.mem_top : a - κ • w ∈ Submodule.span ℝ (Set.range b))
    exact sub_eq_zero.1 (dotProduct_self_eq_zero.1 h0)
  -- `0 < β* < 1`: a small multiple of `x₀` is in `Z`, and `x₀` itself is not
  have hβ0 : 0 < βstar :=
    lt_of_lt_of_le (by positivity : 0 < ε / (2 * (‖x₀‖ + 1))) (hβ.2 (hsmall x₀))
  have hβ1 : βstar < 1 := by
    by_contra h1
    have hmem := (Zonotope.convex_construct Z).smul_mem_of_zero_mem h0Z hβ.1
      ⟨(inv_pos.2 hβ0).le, inv_le_one_of_one_le₀ (not_lt.1 h1)⟩
    rw [smul_smul, inv_mul_cancel₀ hβ0.ne', one_smul] at hmem
    exact hx₀ hmem
  -- `wᵀx* > 0`, as a small multiple of `w` is in `Z`, so `κ > 0`
  have hwx : 0 < w ⬝ᵥ (βstar • x₀) := by
    have h := hmax _ (hsmall w)
    rw [dotProduct_smul, smul_eq_mul] at h
    exact lt_of_lt_of_le (mul_pos (by positivity) hww) h
  have hwx₀ : 0 < w ⬝ᵥ x₀ := by
    rw [dotProduct_smul, smul_eq_mul] at hwx
    exact pos_of_mul_pos_right hwx hβ0.le
  have hκ : 0 < κ := div_pos (by rw [haw, dotProduct_comm]; exact hwx₀) hww
  have hax : ∀ x, a ⬝ᵥ x = κ * (w ⬝ᵥ x) := fun x => by rw [haκ, smul_dotProduct, smul_eq_mul]
  rw [hs]
  refine ⟨fun y hy => ?_, ?_, ?_⟩
  · -- `aᵀy = κ wᵀy ≤ κ wᵀx*`
    show a ⬝ᵥ y ≤ a ⬝ᵥ (βstar • x₀)
    rw [hax, hax]
    exact mul_le_mul_of_nonneg_left (hmax y hy) hκ.le
  · -- `aᵀx* = β* aᵀx₀ < aᵀx₀`
    show a ⬝ᵥ (βstar • x₀) < a ⬝ᵥ x₀
    have hpos : 0 < a ⬝ᵥ x₀ := by rw [hax]; exact mul_pos hκ hwx₀
    rw [dotProduct_smul, smul_eq_mul]
    nlinarith
  · -- `aᵀx = aᵀx*` on `Z` is `wᵀx = max_Z wᵀ`
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hx, hax'⟩
      refine ⟨hx, fun y hy => ?_⟩
      rw [hax, hax] at hax'
      have := mul_left_cancel₀ hκ.ne' hax'
      rw [this]
      exact hmax y hy
    · rintro ⟨hx, hxmax⟩
      refine ⟨hx, ?_⟩
      rw [hax, hax, le_antisymm (hmax x hx) (hxmax _ hβ.1)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
