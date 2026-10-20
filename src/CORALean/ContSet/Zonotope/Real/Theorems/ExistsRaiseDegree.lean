module

public import CORALean.ContSet.Zonotope.Real.Definitions.Degree
public import CORALean.ContSet.Zonotope.Real.Theorems.ExistsFacetSuperset
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# Moving a point along one generator raises its degree

[1, Lemma 3.4]: for `x ∈ Z` with `deg(x) < n - 1` there are `γ` and a generator `g` such that
`x* := x + γg` and `x` lie in a common facet and `deg(x) < deg(x*) ≤ n - 1`. For a full-dimensional
`Z`, which a facet needs; `γ` signed, as the paper's normalized generator set (Eq. 11) holds `±g`.
The proof is the paper's: the least face `F = F(x)` through `x` lies in a facet `F′`
(`exists_facet_superset`), and `F′` has a generator `gⱼ` that the direction `l` of `F` does not
annihilate. `x`'s coefficient there is `±1`; `x* = x - βⱼgⱼ` sets it to `0`, so `x* ± gⱼ ∈ Z`. A
face `G ∋ x*` then contains `x* ± gⱼ`, hence `x`, so has `F`'s affine hull, and `G`'s affine hull
contains it and `gⱼ ∉` it. "Found in polynomial time" is a running time, not stated here.

## Inputs
* `Z` – zonotope
* `x` – point of the zonotope

## Hypotheses
* `hfull` – generators span the space
* `hx` – `x` lies in `Z`
* `hdeg` – degree of `x` below `n - 1`

## Conclusion
* a step along a generator raises the degree

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A full-dimensional zonotope has dimension `n`. -/
theorem Zonotope.aux_finrank_vectorSpan_erd (Z : Zonotope (Vec ℝ n))
    (hfull : Submodule.span ℝ (Set.range Z.G) = ⊤) :
    Module.finrank ℝ (vectorSpan ℝ Z.construct) = n := by
  rw [Zonotope.vectorSpan_construct, hfull, finrank_top]
  exact Module.finrank_fin_fun ℝ

/-- A functional is constant on its exposed face, so it vanishes on the face's affine hull. -/
theorem Zonotope.aux_apply_eq_zero_erd (A : Set (Vec ℝ n)) (l : StrongDual ℝ (Vec ℝ n))
    {w : Vec ℝ n} (hw : w ∈ vectorSpan ℝ {x | x ∈ A ∧ ∀ y ∈ A, l y ≤ l x}) : -- --- CONCL ---
    l w = 0 := by -- --- PROOF ---
  have hle : vectorSpan ℝ {x | x ∈ A ∧ ∀ y ∈ A, l y ≤ l x}
      ≤ LinearMap.ker (l : Vec ℝ n →ₗ[ℝ] ℝ) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, vsub_eq_sub,
      map_sub]
    exact sub_eq_zero.mpr (le_antisymm (hb.2 a ha.1) (ha.2 b hb.1))
  exact hle hw

/-- Replacing coefficient `j` by `s` moves the point by `(s - βⱼ)gⱼ`. -/
theorem Zonotope.aux_update_erd (Z : Zonotope (Vec ℝ n)) (β : Fin Z.h → ℝ) (j : Fin Z.h)
    (s : ℝ) : -- --- CONCL ---
    Z.c + ∑ i, (if i = j then s else β i) • Z.G i
      = (Z.c + ∑ i, β i • Z.G i) + (s - β j) • Z.G j := by -- --- PROOF ---
  have h : ∀ i, (if i = j then s else β i) • Z.G i
      = β i • Z.G i + (if i = j then (s - β j) • Z.G j else 0) := fun i => by
    by_cases hi : i = j
    · subst hi
      simp [sub_smul]
    · simp [hi]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp [add_assoc]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 3.4]: for `x ∈ Z` with `deg(x) < n - 1`, a step `x* = x + γgⱼ` along a generator
stays in a facet through `x` and raises the degree, `deg(x) < deg(x*) ≤ n - 1`. -/
theorem Zonotope.exists_raise_degree (Z : Zonotope (Vec ℝ n))
    (hfull : Submodule.span ℝ (Set.range Z.G) = ⊤) {x : Vec ℝ n} (hx : x ∈ Z.construct)
    (hdeg : Zonotope.degree Z.construct x < n - 1) : -- --- CONCL ---
    ∃ (γ : ℝ) (j : Fin Z.h) (F : Set (Vec ℝ n)), IsExposed ℝ Z.construct F ∧
      Module.finrank ℝ (vectorSpan ℝ F) = n - 1 ∧ x ∈ F ∧ x + γ • Z.G j ∈ F ∧
      Zonotope.degree Z.construct x < Zonotope.degree Z.construct (x + γ • Z.G j) ∧
      Zonotope.degree Z.construct (x + γ • Z.G j) ≤ n - 1 := by -- --- PROOF ---
  classical
  have hD : ∀ z ∈ Z.construct, {d | ∃ F : Set (Vec ℝ n), IsExposed ℝ Z.construct F ∧ z ∈ F ∧
      Module.finrank ℝ (vectorSpan ℝ F) = d}.Nonempty := fun z hz =>
    ⟨_, Z.construct, IsExposed.refl _, hz, rfl⟩
  -- `F(x)`, the least face through `x`, the face of `l`
  obtain ⟨F0, hF0, hxF0, hdim0⟩ := Nat.sInf_mem (hD x hx)
  have hk : Module.finrank ℝ (vectorSpan ℝ F0) = Zonotope.degree Z.construct x := hdim0
  obtain ⟨l, rfl⟩ := hF0 ⟨x, hxF0⟩
  have hZ := Z.aux_finrank_vectorSpan_erd hfull
  have hproper : {x | x ∈ Z.construct ∧ ∀ y ∈ Z.construct, l y ≤ l x} ≠ Z.construct :=
    fun h => by
      rw [h, hZ] at hk
      omega
  -- a facet `F′ ⊇ F(x)`, the face of `l'`
  obtain ⟨F', hF', hdim', hsub⟩ := Z.exists_facet_superset hfull hF0 ⟨x, hxF0⟩ hproper
  obtain ⟨l', rfl⟩ := hF' ⟨x, hsub hxF0⟩
  have hvs : ∀ m : StrongDual ℝ (Vec ℝ n),
      vectorSpan ℝ {x | x ∈ Z.construct ∧ ∀ y ∈ Z.construct, m y ≤ m x}
        = Submodule.span ℝ (Set.range (Z.face (m : Vec ℝ n →ₗ[ℝ] ℝ)).G) := fun m => by
    rw [← Zonotope.vectorSpan_construct, Z.construct_face]
    rfl
  -- a generator of `F′` outside the affine hull of `F(x)`
  obtain ⟨j, hj⟩ : ∃ j : Fin Z.h, (Z.face (l' : Vec ℝ n →ₗ[ℝ] ℝ)).G j
      ∉ vectorSpan ℝ {x | x ∈ Z.construct ∧ ∀ y ∈ Z.construct, l y ≤ l x} := by
    by_contra hcon
    push Not at hcon
    have hle : Submodule.span ℝ (Set.range (Z.face (l' : Vec ℝ n →ₗ[ℝ] ℝ)).G)
        ≤ vectorSpan ℝ {x | x ∈ Z.construct ∧ ∀ y ∈ Z.construct, l y ≤ l x} := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hcon j
    rw [← hvs l'] at hle
    have := Submodule.finrank_mono hle
    omega
  -- `gⱼ` is a generator of `F′` (`l' gⱼ = 0`) that `l` does not annihilate
  have hl'j : l' (Z.G j) = 0 := by
    by_contra h0
    apply hj
    have h : (Z.face (l' : Vec ℝ n →ₗ[ℝ] ℝ)).G j = 0 := by simp [Zonotope.face, h0]
    rw [h]
    exact Submodule.zero_mem _
  have hgj : (Z.face (l' : Vec ℝ n →ₗ[ℝ] ℝ)).G j = Z.G j := by simp [Zonotope.face, hl'j]
  rw [hgj] at hj
  have hlj : l (Z.G j) ≠ 0 := fun h0 => by
    apply hj
    rw [hvs l]
    have h : (Z.face (l : Vec ℝ n →ₗ[ℝ] ℝ)).G j = Z.G j := by simp [Zonotope.face, h0]
    rw [← h]
    exact Submodule.subset_span ⟨j, rfl⟩
  -- `x`'s coefficient on `gⱼ` is a sign; `x* = x - βⱼgⱼ` sets it to `0`
  obtain ⟨β, hβ, hxβ⟩ := hx
  have hβj : β j = Real.sign (l (Z.G j)) :=
    Z.coeff_eq_sign_of_mem_argmax (l : Vec ℝ n →ₗ[ℝ] ℝ) hxF0 hβ hxβ j hlj
  have hpin' : ∀ i, l' (Z.G i) ≠ 0 → β i = Real.sign (l' (Z.G i)) := fun i hi =>
    Z.coeff_eq_sign_of_mem_argmax (l' : Vec ℝ n →ₗ[ℝ] ℝ) (hsub hxF0) hβ hxβ i hi
  -- `x*` and `x* ± gⱼ` are in `Z`, and `x*` is in `F′`
  set xs := x + (-β j) • Z.G j with hxs
  have hpt : ∀ s : ℝ, xs + s • Z.G j = Z.c + ∑ i, (if i = j then s else β i) • Z.G i := by
    intro s
    rw [Z.aux_update_erd β j s, ← hxβ, hxs]
    module
  have hmemS : ∀ s : ℝ, |s| ≤ 1 → xs + s • Z.G j ∈ Z.construct := fun s hs =>
    ⟨fun i => if i = j then s else β i, fun i => by by_cases h : i = j <;> simp [h, hs, hβ i],
      hpt s⟩
  have hxsZ : xs ∈ Z.construct := by
    have := hmemS 0 (by simp)
    rwa [zero_smul, add_zero] at this
  -- on `F′` coefficient `j` is free, the others keep their signs
  have hxsF' : xs ∈ {x | x ∈ Z.construct ∧ ∀ y ∈ Z.construct, l' y ≤ l' x} := by
    refine (Z.mem_argmax_iff (l' : Vec ℝ n →ₗ[ℝ] ℝ) xs).mpr
      ⟨fun i => if i = j then 0 else β i, fun i => ?_, fun i hi => ?_, ?_⟩
    · by_cases h : i = j <;> simp [h, hβ i]
    · by_cases h : i = j
      · subst h
        exact absurd hl'j hi
      · simp only [h, if_false]
        exact hpin' i hi
    · have := hpt 0
      rwa [zero_smul, add_zero] at this
  refine ⟨-β j, j, _, hF', hdim', hsub hxF0, hxsF', ?_, Nat.sInf_le ⟨_, hF', hxsF', hdim'⟩⟩
  -- any face `G ∋ x*` is the face of some `m`, and `m gⱼ = 0`
  obtain ⟨G, hG, hxsG, hdimG⟩ := Nat.sInf_mem (hD xs hxsZ)
  have hkG : Module.finrank ℝ (vectorSpan ℝ G) = Zonotope.degree Z.construct xs := hdimG
  obtain ⟨m, rfl⟩ := hG ⟨xs, hxsG⟩
  have hp := hxsG.2 _ (hmemS 1 (by simp))
  have hm1 := hxsG.2 _ (hmemS (-1) (by simp))
  simp only [map_add, map_smul, smul_eq_mul, one_mul, neg_one_mul] at hp hm1
  have hmg : m (Z.G j) = 0 := by linarith
  have hmx : ∀ s, m (xs + s • Z.G j) = m xs := fun s => by
    rw [map_add, map_smul, hmg, smul_zero, add_zero]
  have hxZ : x ∈ Z.construct := ⟨β, hβ, hxβ⟩
  have hxeq : x = xs + β j • Z.G j := by
    rw [hxs]
    module
  have hxG : ∀ y ∈ Z.construct, m y ≤ m x := fun y hy => by
    rw [hxeq, hmx]
    exact hxsG.2 y hy
  -- the face `H` of `m + l` is through `x` and in both `F(x)` and `G`
  set H := {z | z ∈ Z.construct ∧ ∀ y ∈ Z.construct, (m + l) y ≤ (m + l) z} with hHdef
  have hxH : x ∈ H := ⟨hxZ, fun y hy => by
    simp only [_root_.add_apply]
    linarith [hxG y hy, hxF0.2 y hy]⟩
  have hkH : Zonotope.degree Z.construct x ≤ Module.finrank ℝ (vectorSpan ℝ H) :=
    Nat.sInf_le ⟨H, fun _ => ⟨m + l, rfl⟩, hxH, rfl⟩
  have hHF0 : H ⊆ {x | x ∈ Z.construct ∧ ∀ y ∈ Z.construct, l y ≤ l x} := fun z hz => by
    have h1 := hz.2 x hxZ
    have h2 := hxG z hz.1
    simp only [_root_.add_apply] at h1
    exact ⟨hz.1, fun y hy => by linarith [hxF0.2 y hy]⟩
  have hHG : H ⊆ {x | x ∈ Z.construct ∧ ∀ y ∈ Z.construct, m y ≤ m x} := fun z hz => by
    have h1 := hz.2 x hxZ
    have h2 := hxF0.2 z hz.1
    simp only [_root_.add_apply] at h1
    exact ⟨hz.1, fun y hy => by linarith [hxG y hy]⟩
  have heq : vectorSpan ℝ H = vectorSpan ℝ {x | x ∈ Z.construct ∧ ∀ y ∈ Z.construct, l y ≤ l x} :=
    Submodule.eq_of_le_of_finrank_le (vectorSpan_mono ℝ hHF0) (by omega)
  -- `gⱼ` is in the affine hull of `G` and not in that of `F(x)`
  have hlt : vectorSpan ℝ {x | x ∈ Z.construct ∧ ∀ y ∈ Z.construct, l y ≤ l x}
      < vectorSpan ℝ {x | x ∈ Z.construct ∧ ∀ y ∈ Z.construct, m y ≤ m x} := by
    refine lt_of_le_of_ne (heq.symm.le.trans (vectorSpan_mono ℝ hHG)) fun hne => ?_
    have hg1 : xs + (1 : ℝ) • Z.G j ∈ {x | x ∈ Z.construct ∧ ∀ y ∈ Z.construct, m y ≤ m x} :=
      ⟨hmemS 1 (by simp), fun y hy => by rw [hmx]; exact hxsG.2 y hy⟩
    have hgG := vsub_mem_vectorSpan ℝ hg1 hxsG
    rw [vsub_eq_sub, one_smul, add_sub_cancel_left, ← hne] at hgG
    exact hlj (Zonotope.aux_apply_eq_zero_erd _ l hgG)
  rw [← hxs, ← hk, ← hkG]
  exact Submodule.finrank_lt_finrank_of_lt hlt

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
