import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The irredundant rows of a full-dimensional polyhedron describe it

For `P = {x | Cⱼx ≤ dⱼ for every row j}` with nonempty interior, in which two rows cut the same
halfspace only if it is the whole space, dropping every redundant row at once leaves `P`. A row
is redundant when the others already imply it. Each redundant row on its own being droppable does
not give it — two rows cutting the same halfspace are each redundant and jointly are not — which
is the gap [1, Prop. 2] leaves, and which `gen_not_required_iff` carried as its hypothesis `hmin`.

Rows are dropped one at a time. Two redundant rows `j ≠ k`: if some `y` met every row but `j` and
`k` and broke `k`, it breaks `j` too. From a `z` interior to `P`, row `i` is crossed on `[z, y]` at
`tᵢ = pᵢ/(pᵢ + qᵢ)` (`pᵢ` its slack at `z`, `qᵢ` its excess at `y`); `t_j = t_k` is the affine
equation `p_j q_k = p_k q_j` in `z`, which holds on the open interior only if the rows are
proportional, the same halfspace. So for some `z` one crossing comes first, and between the two
crossings lies a point breaking that row alone, which is then not redundant.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {ι E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A neighbourhood of `z` holds a positive step along every direction. -/
theorem Zonotope.aux_exists_pos_mem_rdr {U : Set E} {z : E} (hU : U ∈ nhds z) (v : E) :
    ∃ s : ℝ, 0 < s ∧ z + s • v ∈ U := by -- --- PROOF ---
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hv : 0 ≤ ‖v‖ := norm_nonneg v
  refine ⟨ε / (2 * (‖v‖ + 1)), by positivity, hball ?_⟩
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

/-- A row some point breaks is strict at an interior point. -/
theorem Zonotope.aux_strict_rdr (C : ι → E →ₗ[ℝ] ℝ) (d : ι → ℝ) {p : ι → Prop} {z y : E}
    (hz : z ∈ interior {x | ∀ j, p j → C j x ≤ d j}) {j : ι} (hj : p j) (hy : d j < C j y) :
    C j z < d j := by -- --- PROOF ---
  obtain ⟨s, hs, hmem⟩ := Zonotope.aux_exists_pos_mem_rdr (mem_interior_iff_mem_nhds.mp hz) (y - z)
  have h := hmem j hj
  have hzP := (interior_subset hz : z ∈ {x | ∀ j, p j → C j x ≤ d j}) j hj
  rw [map_add, map_smul, map_sub, smul_eq_mul] at h
  nlinarith

/-- Two crossing parameters that differ: past the first, before the second, only the first row is
broken. -/
theorem Zonotope.aux_one_side_rdr (C : ι → E →ₗ[ℝ] ℝ) (d : ι → ℝ) {p : ι → Prop} {j k : ι}
    {z y : E} (hzP : ∀ i, p i → C i z ≤ d i) (hzj : C j z < d j) (hzk : C k z < d k)
    (hy : ∀ i, p i → i ≠ j → i ≠ k → C i y ≤ d i) (hyj : d j < C j y) (hyk : d k < C k y)
    (hlt : (d j - C j z) * (C k y - d k) < (d k - C k z) * (C j y - d j)) :
    ∃ x, (∀ i, p i → i ≠ j → C i x ≤ d i) ∧ d j < C j x := by -- --- PROOF ---
  set pj := d j - C j z
  set pk := d k - C k z
  set qj := C j y - d j
  set qk := C k y - d k
  have hpj : 0 < pj := by linarith
  have hpk : 0 < pk := by linarith
  have hqj : 0 < qj := by linarith
  have hqk : 0 < qk := by linarith
  -- the two crossing parameters, `t_j < t_k`, and `t` between them
  have htt : pj / (pj + qj) < pk / (pk + qk) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  set t := (pj / (pj + qj) + pk / (pk + qk)) / 2 with ht
  have h1 : pj < t * (pj + qj) := by
    rw [← div_lt_iff₀ (by linarith)]
    linarith
  have h2 : t * (pk + qk) < pk := by
    rw [← lt_div_iff₀ (by linarith)]
    linarith
  -- `t` is a parameter on the segment
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by
    have : pk / (pk + qk) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    have : pj / (pj + qj) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  have happ : ∀ i, C i (z + t • (y - z)) = C i z + t * (C i y - C i z) := fun i => by
    rw [map_add, map_smul, map_sub, smul_eq_mul]
  refine ⟨z + t • (y - z), fun i hi hij => ?_, ?_⟩
  · rw [happ]
    by_cases hik : i = k
    · subst hik
      nlinarith
    · -- every other row holds at both ends, so on the whole segment
      have hzi := hzP i hi
      have hyi := hy i hi hij hik
      nlinarith
  · rw [happ]
    nlinarith

/-- With full dimension and no repeated proper halfspace, a redundant row stays redundant once
another redundant row is dropped. -/
theorem Zonotope.aux_pair_rdr (C : ι → E →ₗ[ℝ] ℝ) (d : ι → ℝ) (p : ι → Prop)
    (hint : (interior {x | ∀ j, p j → C j x ≤ d j}).Nonempty)
    (hdist : ∀ j k, p j → p k → j ≠ k → {x | C j x ≤ d j} = {x | C k x ≤ d k} →
      {x : E | C j x ≤ d j} = Set.univ)
    {j k : ι} (hpj : p j) (hpk : p k) (hjk : j ≠ k)
    (hj : {x | ∀ i, p i → i ≠ j → C i x ≤ d i} ⊆ {x | C j x ≤ d j})
    (hk : {x | ∀ i, p i → i ≠ k → C i x ≤ d i} ⊆ {x | C k x ≤ d k}) :
    {x | ∀ i, p i → i ≠ j → i ≠ k → C i x ≤ d i} ⊆ {x | C k x ≤ d k} := by -- --- PROOF ---
  intro y hy
  by_contra hyk
  have hyk : d k < C k y := lt_of_not_ge hyk
  -- `y` breaks `j` as well, or `k` would not be redundant
  have hyj : d j < C j y := by
    by_contra hyj
    refine absurd (hk fun i hi hik => ?_) (not_le.mpr hyk)
    by_cases hij : i = j
    · subst hij
      exact le_of_not_gt hyj
    · exact hy i hi hij hik
  -- an interior point at which the two crossings differ
  obtain ⟨z0, hz0⟩ := hint
  obtain ⟨z, hz, hne⟩ : ∃ z ∈ interior {x | ∀ j, p j → C j x ≤ d j},
      (d j - C j z) * (C k y - d k) ≠ (d k - C k z) * (C j y - d j) := by
    by_contra hcon
    push Not at hcon
    have hlin : ∀ v, (C k y - d k) * C j v = (C j y - d j) * C k v := fun v => by
      obtain ⟨s, hs, hmem⟩ := Zonotope.aux_exists_pos_mem_rdr
        (isOpen_interior.mem_nhds hz0) v
      have e1 := hcon z0 hz0
      have e2 := hcon _ hmem
      rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at e2
      have : s * ((C k y - d k) * C j v - (C j y - d j) * C k v) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    have hoff : (C k y - d k) * d j = (C j y - d j) * d k := by
      have e1 := hcon z0 hz0
      have := hlin z0
      linarith
    -- the two rows are proportional, so cut the same halfspace, a proper one
    have hqj : 0 < C j y - d j := by linarith
    have hqk : 0 < C k y - d k := by linarith
    have hsame : {x | C j x ≤ d j} = {x | C k x ≤ d k} := by
      ext x
      have := hlin x
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        by_contra h'
        nlinarith
      · intro h
        by_contra h'
        nlinarith
    have huniv := hdist j k hpj hpk hjk hsame
    have hymem : y ∈ {x : E | C j x ≤ d j} := huniv ▸ Set.mem_univ y
    exact absurd hymem (not_le.mpr hyj)
  have hzP : ∀ i, p i → C i z ≤ d i := interior_subset hz
  have hzj := Zonotope.aux_strict_rdr C d hz hpj hyj
  have hzk := Zonotope.aux_strict_rdr C d hz hpk hyk
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `j` is crossed first: a point breaking `j` alone
    obtain ⟨x, hx, hxj⟩ := Zonotope.aux_one_side_rdr C d hzP hzj hzk hy hyj hyk hlt
    exact absurd (hj hx) (not_le.mpr hxj)
  · obtain ⟨x, hx, hxk⟩ := Zonotope.aux_one_side_rdr C d hzP hzk hzj
      (fun i hi hik hij => hy i hi hij hik) hyk hyj hgt
    exact absurd (hk hx) (not_le.mpr hxk)


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2]: in a full-dimensional polyhedron with no repeated proper halfspace, the redundant
rows `Red` can all be dropped at once. -/
theorem Zonotope.rows_eq_drop_redundant (C : ι → E →ₗ[ℝ] ℝ) (d : ι → ℝ) (Red : Finset ι)
    (p : ι → Prop) (hint : (interior {x | ∀ j, p j → C j x ≤ d j}).Nonempty)
    (hdist : ∀ j k, p j → p k → j ≠ k → {x | C j x ≤ d j} = {x | C k x ≤ d k} →
      {x : E | C j x ≤ d j} = Set.univ)
    (hRed : ∀ j ∈ Red, p j → {x | ∀ k, p k → k ≠ j → C k x ≤ d k} ⊆ {x | C j x ≤ d j}) :
    {x | ∀ j, p j → C j x ≤ d j} = {x | ∀ j, p j → j ∉ Red → C j x ≤ d j} := by -- --- PROOF ---
  classical
  induction Red using Finset.induction_on generalizing p with
  | empty => simp
  | insert a R haR ih =>
    by_cases hpa : p a
    · -- drop `a` first: the rest keep `P` and stay redundant
      set p' : ι → Prop := fun i => p i ∧ i ≠ a with hp'
      have hP : {x | ∀ j, p j → C j x ≤ d j} = {x | ∀ j, p' j → C j x ≤ d j} := by
        ext x
        refine ⟨fun h j hj => h j hj.1, fun h j hj => ?_⟩
        by_cases hja : j = a
        · subst hja
          exact hRed j (Finset.mem_insert_self _ _) hj fun k hk hkj => h k ⟨hk, hkj⟩
        · exact h j ⟨hj, hja⟩
      have hR : ∀ j ∈ R, p' j → {x | ∀ k, p' k → k ≠ j → C k x ≤ d k} ⊆ {x | C j x ≤ d j} := by
        intro j hjR hj x hx
        exact Zonotope.aux_pair_rdr C d p hint hdist hpa hj.1 (Ne.symm hj.2)
          (hRed a (Finset.mem_insert_self _ _) hpa)
          (hRed j (Finset.mem_insert_of_mem hjR) hj.1)
          (fun k hk hka hkj => hx k ⟨hk, hka⟩ hkj)
      rw [hP, ih p' (hP ▸ hint) (fun j k hj hk => hdist j k hj.1 hk.1) hR]
      ext x
      simp only [Set.mem_setOf_eq, Finset.mem_insert, not_or, hp']
      exact ⟨fun h j hj ⟨hja, hjR⟩ => h j ⟨hj, hja⟩ hjR, fun h j hj hjR => h j hj.1 ⟨hj.2, hjR⟩⟩
    · -- `a` is not a row at all
      rw [ih p hint hdist fun j hj => hRed j (Finset.mem_insert_of_mem hj)]
      ext x
      simp only [Set.mem_setOf_eq, Finset.mem_insert, not_or]
      refine ⟨fun h j hj ⟨hja, hjR⟩ => h j hj hjR, fun h j hj hjR => h j hj ⟨?_, hjR⟩⟩
      rintro rfl
      exact hpa hj

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
