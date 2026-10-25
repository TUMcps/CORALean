module

public import CORALean.ContSet.Zonotope.Real.Theorems.ConstructFace
public import CORALean.ContSet.Zonotope.Real.Theorems.VectorSpanConstruct
public import CORALean.Global.Tensor
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-!
# Every proper face of a full-dimensional zonotope lies in a facet

For `Z ⊆ ℝⁿ` whose generators span, every nonempty exposed face other than `Z` lies in an exposed
face of dimension `n - 1`, a facet: what [1, Lemma 3.4] uses ("there is a facet `F′ ⊇ F`"). The
face maximizing `l` is `Z.face l` (`construct_face`), of dimension the rank `k` of the generators
`l` annihilates. While `k ≤ n - 2`, a functional `v` vanishing on those generators but not on
`ker l` exists; oriented to agree with `l` on some generator, `l - tv` with `t` the first ratio
`l gⱼ / v gⱼ` keeps every sign of `l` or zeroes it and annihilates one more independent generator,
so its face contains `l`'s and has larger dimension. It stays `≠ 0`, the generators spanning.

## Inputs
* `Z` – zonotope
* `F` – face

## Hypotheses
* `hfull` – generators span the space
* `hF` – `F` is an exposed face
* `hne` – `F` nonempty
* `hproper` – `F` is not all of `Z`

## Conclusion
* `F` lies in an exposed face of codimension one

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- An annihilated generator is in the span of the face's generators. -/
theorem Zonotope.aux_mem_span_face_efs (Z : Zonotope (Vec ℝ n)) (l : Vec ℝ n →ₗ[ℝ] ℝ)
    {j : Fin Z.h} (hj : l (Z.G j) = 0) :
    Z.G j ∈ Submodule.span ℝ (Set.range (Z.face l).G) := by
  have h : (Z.face l).G j = Z.G j := by
    simp [Zonotope.face, hj]
  rw [← h]
  exact Submodule.subset_span ⟨j, rfl⟩

/-- A functional vanishing on the generators `l` annihilates vanishes on their span. -/
theorem Zonotope.aux_apply_eq_zero_efs (Z : Zonotope (Vec ℝ n)) (l m : Vec ℝ n →ₗ[ℝ] ℝ)
    (hm : ∀ j, l (Z.G j) = 0 → m (Z.G j) = 0) {w : Vec ℝ n}
    (hw : w ∈ Submodule.span ℝ (Set.range (Z.face l).G)) : -- --- CONCL ---
    m w = 0 := by -- --- PROOF ---
  have hle : Submodule.span ℝ (Set.range (Z.face l).G) ≤ LinearMap.ker m := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    by_cases hj : l (Z.G j) = 0
    · simp [Zonotope.face, hj, hm j hj]
    · simp [Zonotope.face, hj]
  exact hle hw

/-- A functional vanishing on spanning generators vanishes. -/
theorem Zonotope.aux_eq_zero_efs (Z : Zonotope (Vec ℝ n))
    (hfull : Submodule.span ℝ (Set.range Z.G) = ⊤) (m : Vec ℝ n →ₗ[ℝ] ℝ)
    (hm : ∀ j, m (Z.G j) = 0) (y : Vec ℝ n) : -- --- CONCL ---
    m y = 0 := by -- --- PROOF ---
  have hle : Submodule.span ℝ (Set.range Z.G) ≤ LinearMap.ker m := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hm j
  rw [hfull] at hle
  exact hle Submodule.mem_top

/-- Two reals with a positive product have the same sign. -/
theorem Zonotope.aux_sign_eq_efs {a b : ℝ} (h : 0 < a * b) : Real.sign a = Real.sign b := by
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [Real.sign_of_pos ha, Real.sign_of_pos hb]
  · rw [Real.sign_of_neg ha, Real.sign_of_neg hb]

/-- A functional agreeing in sign with `l` wherever it is nonzero has a face containing `l`'s. -/
theorem Zonotope.aux_argmax_subset_efs (Z : Zonotope (Vec ℝ n)) (l l' : Vec ℝ n →ₗ[ℝ] ℝ)
    (h : ∀ j, l' (Z.G j) ≠ 0 → 0 < l (Z.G j) * l' (Z.G j)) : -- --- CONCL ---
    {x | x ∈ Z.construct ∧ ∀ y ∈ Z.construct, l y ≤ l x}
      ⊆ {x | x ∈ Z.construct ∧ ∀ y ∈ Z.construct, l' y ≤ l' x} := by -- --- PROOF ---
  intro x hx
  obtain ⟨β, hβ, hpin, hxβ⟩ := (Z.mem_argmax_iff l x).mp hx
  refine (Z.mem_argmax_iff l' x).mpr ⟨β, hβ, fun j hj => ?_, hxβ⟩
  have hp := h j hj
  have hl : l (Z.G j) ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hp
    exact lt_irrefl _ hp
  rw [hpin j hl, aux_sign_eq_efs hp]

/-- One step: a face of dimension at most `n - 2` lies in a face of larger dimension. -/
theorem Zonotope.aux_step_efs (Z : Zonotope (Vec ℝ n))
    (hfull : Submodule.span ℝ (Set.range Z.G) = ⊤) (l : Vec ℝ n →ₗ[ℝ] ℝ)
    (hdim : Module.finrank ℝ (Submodule.span ℝ (Set.range (Z.face l).G)) + 2 ≤ n) : -- --- CONCL ---
    ∃ l' : Vec ℝ n →ₗ[ℝ] ℝ, (∃ j, l' (Z.G j) ≠ 0) ∧
      Submodule.span ℝ (Set.range (Z.face l).G) < Submodule.span ℝ (Set.range (Z.face l').G) ∧
      ∀ j, l' (Z.G j) ≠ 0 → 0 < l (Z.G j) * l' (Z.G j) := by -- --- PROOF ---
  classical
  set W := Submodule.span ℝ (Set.range (Z.face l).G) with hW
  have hWl : W ≤ LinearMap.ker l := fun w hw =>
    Z.aux_apply_eq_zero_efs l l (fun _ h => h) hw
  -- `ker l` is a hyperplane, so it is not inside `W`
  have hker : n - 1 ≤ Module.finrank ℝ (LinearMap.ker l) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker l
    have h2 : Module.finrank ℝ (LinearMap.range l) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range l)
      rwa [Module.finrank_self] at this
    have h3 : Module.finrank ℝ (Vec ℝ n) = n := Module.finrank_fin_fun ℝ
    omega
  obtain ⟨y, hyk, hyW⟩ : ∃ y ∈ LinearMap.ker l, y ∉ W := by
    by_contra hcon
    push Not at hcon
    have := Submodule.finrank_mono (show LinearMap.ker l ≤ W from hcon)
    omega
  obtain ⟨f, hfy, hfW⟩ := W.exists_dual_map_eq_bot_of_notMem hyW inferInstance
  have hfW' : ∀ w ∈ W, f w = 0 := fun w hw => by
    have h : f w ∈ W.map f := Submodule.mem_map_of_mem hw
    rw [hfW] at h
    exact (Submodule.mem_bot ℝ).mp h
  -- `f` reaches a generator outside `W`; orient it to agree with `l` there
  obtain ⟨j1, hj1⟩ : ∃ j, f (Z.G j) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hfy (Z.aux_eq_zero_efs hfull f hcon y)
  have hlj1 : l (Z.G j1) ≠ 0 := fun h0 => hj1 (hfW' _ (Z.aux_mem_span_face_efs l h0))
  obtain ⟨v, hvW, hvy, hpos⟩ : ∃ v : Vec ℝ n →ₗ[ℝ] ℝ, (∀ w ∈ W, v w = 0) ∧ v y ≠ 0 ∧
      ∃ j, 0 < l (Z.G j) * v (Z.G j) := by
    rcases lt_or_gt_of_ne (mul_ne_zero hlj1 hj1) with hneg | hpos
    · refine ⟨-f, fun w hw => by simp [hfW' w hw], by simpa using hfy, j1, ?_⟩
      simp only [LinearMap.neg_apply, mul_neg]
      linarith
    · exact ⟨f, hfW', hfy, j1, hpos⟩
  have hvS : ∀ j, l (Z.G j) = 0 → v (Z.G j) = 0 := fun j hj =>
    hvW _ (Z.aux_mem_span_face_efs l hj)
  -- the first generator whose sign `l - t v` zeroes, as `t` grows from `0`
  set T := Finset.univ.filter fun j => 0 < l (Z.G j) * v (Z.G j) with hT
  have hTne : T.Nonempty := by
    obtain ⟨j, hj⟩ := hpos
    exact ⟨j, by simp [hT, hj]⟩
  obtain ⟨j0, hj0T, hj0min⟩ := T.exists_min_image (fun j => l (Z.G j) / v (Z.G j)) hTne
  have hj0 : 0 < l (Z.G j0) * v (Z.G j0) := (Finset.mem_filter.mp hj0T).2
  have hv0 : v (Z.G j0) ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hj0
    exact lt_irrefl _ hj0
  have hl0 : l (Z.G j0) ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hj0
    exact lt_irrefl _ hj0
  -- `t`, that first ratio, is positive
  set t := l (Z.G j0) / v (Z.G j0) with ht
  have htpos : 0 < t := by
    have h : t = l (Z.G j0) * v (Z.G j0) / (v (Z.G j0) * v (Z.G j0)) := by
      rw [ht, mul_div_mul_right _ _ hv0]
    rw [h]
    exact div_pos hj0 (mul_self_pos.mpr hv0)
  have happ : ∀ j, (l - t • v) (Z.G j) = l (Z.G j) - t * v (Z.G j) := fun j => by simp
  refine ⟨l - t • v, ?_, ?_, ?_⟩
  · -- `l - t v` is not zero at `y`, so not on every generator
    by_contra hcon
    push Not at hcon
    have h := Z.aux_eq_zero_efs hfull _ hcon y
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.mem_ker.mp hyk, zero_sub,
      neg_eq_zero, smul_eq_mul] at h
    exact hvy ((mul_eq_zero.mp h).resolve_left htpos.ne')
  · -- `l - t v` annihilates every generator `l` does, and `g_{j₀}` besides
    have hS : ∀ j, l (Z.G j) = 0 → (l - t • v) (Z.G j) = 0 := fun j hj => by
      rw [happ, hj, hvS j hj, mul_zero, sub_zero]
    have hle : W ≤ Submodule.span ℝ (Set.range (Z.face (l - t • v)).G) := by
      rw [hW, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      by_cases hj : l (Z.G j) = 0
      · have h : (Z.face l).G j = Z.G j := by simp [Zonotope.face, hj]
        rw [h]
        exact Z.aux_mem_span_face_efs _ (hS j hj)
      · have h : (Z.face l).G j = 0 := by simp [Zonotope.face, hj]
        rw [h]
        exact Submodule.zero_mem _
    refine lt_of_le_of_ne hle fun heq => ?_
    have hz : (l - t • v) (Z.G j0) = 0 := by
      rw [happ, ht, div_mul_cancel₀ _ hv0, sub_self]
    have hmem := Z.aux_mem_span_face_efs _ hz
    rw [← heq] at hmem
    exact hl0 (LinearMap.mem_ker.mp (hWl hmem))
  · -- every sign of `l - t v` is `l`'s: `t` is at most each ratio where `l` and `v` agree
    intro j hj
    rw [happ] at hj ⊢
    have hlj : l (Z.G j) ≠ 0 := fun h0 => hj (by rw [h0, hvS j h0, mul_zero, sub_zero])
    have hnn : 0 ≤ l (Z.G j) * (l (Z.G j) - t * v (Z.G j)) := by
      by_cases hjT : 0 < l (Z.G j) * v (Z.G j)
      · have hmin : t ≤ l (Z.G j) / v (Z.G j) := hj0min j (by simp [hT, hjT])
        have hvj : v (Z.G j) ≠ 0 := fun h0 => by
          rw [h0, mul_zero] at hjT
          exact lt_irrefl _ hjT
        have h1 : t * (l (Z.G j) * v (Z.G j))
            ≤ l (Z.G j) / v (Z.G j) * (l (Z.G j) * v (Z.G j)) :=
          mul_le_mul_of_nonneg_right hmin hjT.le
        have h2 : l (Z.G j) / v (Z.G j) * (l (Z.G j) * v (Z.G j)) = l (Z.G j) * l (Z.G j) := by
          field_simp
        nlinarith
      · push Not at hjT
        nlinarith [mul_self_nonneg (l (Z.G j)), mul_nonneg htpos.le (neg_nonneg.mpr hjT)]
    exact lt_of_le_of_ne hnn (mul_ne_zero hlj hj).symm

/-- Iterating the step until the face has dimension at least `n - 1`. -/
theorem Zonotope.aux_exists_top_efs (Z : Zonotope (Vec ℝ n))
    (hfull : Submodule.span ℝ (Set.range Z.G) = ⊤) (k : ℕ) : -- --- CONCL ---
    ∀ l : Vec ℝ n →ₗ[ℝ] ℝ,
      n - Module.finrank ℝ (Submodule.span ℝ (Set.range (Z.face l).G)) = k →
      (∃ j, l (Z.G j) ≠ 0) → ∃ l' : Vec ℝ n →ₗ[ℝ] ℝ, (∃ j, l' (Z.G j) ≠ 0) ∧
        n ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range (Z.face l').G)) + 1 ∧
        {x | x ∈ Z.construct ∧ ∀ y ∈ Z.construct, l y ≤ l x}
          ⊆ {x | x ∈ Z.construct ∧ ∀ y ∈ Z.construct, l' y ≤ l' x} := by -- --- PROOF ---
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro l hk hl
    by_cases hd : Module.finrank ℝ (Submodule.span ℝ (Set.range (Z.face l).G)) + 2 ≤ n
    · obtain ⟨l', hl', hlt, hsign⟩ := Z.aux_step_efs hfull l hd
      have h1 := Submodule.finrank_lt_finrank_of_lt hlt
      have h2 := Submodule.finrank_le (Submodule.span ℝ (Set.range (Z.face l').G))
      have h3 : Module.finrank ℝ (Vec ℝ n) = n := Module.finrank_fin_fun ℝ
      obtain ⟨l'', hl'', hdim'', hsub''⟩ := ih _ (by omega) l' rfl hl'
      exact ⟨l'', hl'', hdim'', (Z.aux_argmax_subset_efs l l' hsign).trans hsub''⟩
    · exact ⟨l, hl, by omega, subset_rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 3.4]: a nonempty exposed face of a full-dimensional zonotope other than the
zonotope lies in an exposed face of dimension `n - 1`. -/
theorem Zonotope.exists_facet_superset (Z : Zonotope (Vec ℝ n))
    (hfull : Submodule.span ℝ (Set.range Z.G) = ⊤) {F : Set (Vec ℝ n)}
    (hF : IsExposed ℝ Z.construct F) (hne : F.Nonempty)
    (hproper : F ≠ Z.construct) : -- --- CONCL ---
    ∃ F' : Set (Vec ℝ n), IsExposed ℝ Z.construct F' ∧
      Module.finrank ℝ (vectorSpan ℝ F') = n - 1 ∧ F ⊆ F' := by -- --- PROOF ---
  obtain ⟨l, rfl⟩ := hF hne
  -- `l` reaches some generator, or its face would be all of `Z`
  have hl : ∃ j, (l : Vec ℝ n →ₗ[ℝ] ℝ) (Z.G j) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hproper
    have h0 := Z.aux_eq_zero_efs hfull _ hcon
    ext x
    simp only [ContinuousLinearMap.coe_coe] at h0
    simp [h0]
  obtain ⟨l', hl', hdim, hsub⟩ := Z.aux_exists_top_efs hfull _ (l : Vec ℝ n →ₗ[ℝ] ℝ) rfl hl
  refine ⟨{x | x ∈ Z.construct ∧ ∀ y ∈ Z.construct, l' y ≤ l' x},
    fun _ => ⟨LinearMap.toContinuousLinearMap l', rfl⟩, ?_, hsub⟩
  rw [← Z.construct_face l', Zonotope.vectorSpan_construct]
  -- the span is proper: `l'` vanishes on it and not on every generator
  have hne' : Submodule.span ℝ (Set.range (Z.face l').G) ≠ ⊤ := fun htop => by
    obtain ⟨j, hj⟩ := hl'
    have h : Z.G j ∈ Submodule.span ℝ (Set.range (Z.face l').G) := htop ▸ Submodule.mem_top
    exact hj (Z.aux_apply_eq_zero_efs l' l' (fun _ h => h) h)
  have h1 : Module.finrank ℝ (Submodule.span ℝ (Set.range (Z.face l').G)) < n :=
    (Submodule.finrank_lt hne').trans_eq (Module.finrank_fin_fun ℝ)
  have h2 : n ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range (Z.face l').G)) + 1 := hdim
  have h3 : Module.finrank ℝ (Submodule.span ℝ (Set.range (Z.face l').G)) = n - 1 := by omega
  exact h3

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
