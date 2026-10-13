import CORALean.ContSet.Zonotope.Real.Operations.Walk
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology

/-!
# The walk of sorted generators encloses a planar zonotope

For generators in the half-plane `y > 0 ∨ (y = 0 ∧ x ≥ 0)`, sorted by angle (`cross(g_i, g_j) ≥ 0`
for `i < j`), the `2 (h + 1)` corners of `Zonotope.walk` have the zonotope in their hull. By
separation it is enough that every linear functional `f` is minimised over the zonotope at a walk
corner, and `f` is at its minimum there when the corner's signs are `-sign (f g_j)`. The signs of
`f g_j` along the sorted generators change at most once: the identity
`cross(i,j) f_l + cross(j,l) f_i = cross(i,l) f_j` rules out `+ - +` and `- + -`, up to parallel
generators, which the half-plane makes point the same way. So the signs are `+ … + - … -` or the
reverse, which is the walk's pattern for some `k`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- In the half-plane, a generator parallel to one that `f` is positive on is not negative. -/
theorem Zonotope.aux_par (p q : ℝ) (u w : Vec ℝ 2) (hu : 0 ≤ u 1 ∧ (0 < u 1 ∨ 0 ≤ u 0))
    (hw : 0 ≤ w 1 ∧ (0 < w 1 ∨ 0 ≤ w 0)) (hc : u 0 * w 1 - u 1 * w 0 = 0)
    (hf : 0 < p * u 0 + q * u 1) : 0 ≤ p * w 0 + q * w 1 := by -- --- PROOF ---
  by_cases hu1 : 0 < u 1
  · -- `w` is a nonnegative multiple of `u`
    have key : (p * w 0 + q * w 1) * u 1 = (p * u 0 + q * u 1) * w 1 := by
      linear_combination (-p) * hc
    have : 0 ≤ (p * w 0 + q * w 1) * u 1 := by rw [key]; exact mul_nonneg hf.le hw.1
    exact nonneg_of_mul_nonneg_left this hu1
  · -- `u` lies on the positive `x`-axis
    have hu1' : u 1 = 0 := le_antisymm (not_lt.mp hu1) hu.1
    have hu0 : 0 < u 0 := by
      rcases hu.2 with h | h
      · exact absurd h hu1
      · rcases h.eq_or_lt with h0 | h0
        · rw [hu1', ← h0] at hf; simp at hf
        · exact h0
    have hw1 : w 1 = 0 := by
      rw [hu1'] at hc
      have : u 0 * w 1 = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hu0.ne'
    have hw0 : 0 ≤ w 0 := by
      rcases hw.2 with h | h
      · rw [hw1] at h; exact absurd h (lt_irrefl 0)
      · exact h
    have hp : 0 < p := by
      rw [hu1'] at hf
      have : 0 < p * u 0 := by linarith
      exact pos_of_mul_pos_left this hu0.le
    rw [hw1]; nlinarith

/-- No sign pattern `+ - +` or `- + -` along sorted generators. -/
theorem Zonotope.aux_noalt (p q : ℝ) (gi gj gl : Vec ℝ 2) (hi : 0 ≤ gi 1 ∧ (0 < gi 1 ∨ 0 ≤ gi 0))
    (hj : 0 ≤ gj 1 ∧ (0 < gj 1 ∨ 0 ≤ gj 0)) (_hl : 0 ≤ gl 1 ∧ (0 < gl 1 ∨ 0 ≤ gl 0))
    (cij : 0 ≤ gi 0 * gj 1 - gi 1 * gj 0) (cjl : 0 ≤ gj 0 * gl 1 - gj 1 * gl 0)
    (cil : 0 ≤ gi 0 * gl 1 - gi 1 * gl 0) :
    ¬(0 < p * gi 0 + q * gi 1 ∧ p * gj 0 + q * gj 1 < 0 ∧ 0 < p * gl 0 + q * gl 1) ∧
      ¬(p * gi 0 + q * gi 1 < 0 ∧ 0 < p * gj 0 + q * gj 1 ∧
        p * gl 0 + q * gl 1 < 0) := by -- --- PROOF ---
  -- the identity `cross(i,j) f_l + cross(j,l) f_i = cross(i,l) f_j`
  have key : (gi 0 * gj 1 - gi 1 * gj 0) * (p * gl 0 + q * gl 1)
      + (gj 0 * gl 1 - gj 1 * gl 0) * (p * gi 0 + q * gi 1)
      = (gi 0 * gl 1 - gi 1 * gl 0) * (p * gj 0 + q * gj 1) := by ring
  constructor
  · rintro ⟨h1, h2, h3⟩
    -- the left side is nonnegative, the right nonpositive: both vanish
    have a1 := mul_nonneg cij h3.le
    have a2 := mul_nonneg cjl h1.le
    have a3 : (gi 0 * gl 1 - gi 1 * gl 0) * (p * gj 0 + q * gj 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos cil h2.le
    have hz : (gi 0 * gj 1 - gi 1 * gj 0) * (p * gl 0 + q * gl 1) = 0 := by linarith
    have hc : gi 0 * gj 1 - gi 1 * gj 0 = 0 :=
      (mul_eq_zero.mp hz).resolve_right h3.ne'
    have := Zonotope.aux_par p q gi gj hi hj hc h1
    linarith
  · rintro ⟨h1, h2, h3⟩
    have a1 := mul_nonpos_of_nonneg_of_nonpos cij h3.le
    have a2 := mul_nonpos_of_nonneg_of_nonpos cjl h1.le
    have a3 : 0 ≤ (gi 0 * gl 1 - gi 1 * gl 0) * (p * gj 0 + q * gj 1) := mul_nonneg cil h2.le
    have hz : (gi 0 * gj 1 - gi 1 * gj 0) * (p * gl 0 + q * gl 1) = 0 := by linarith
    have hc : gi 0 * gj 1 - gi 1 * gj 0 = 0 :=
      (mul_eq_zero.mp hz).resolve_right h3.ne
    have := Zonotope.aux_par (-p) (-q) gi gj hi hj hc (by linarith)
    linarith

/-- With no positive before a negative, the values are `≤ 0` then `≥ 0`. -/
theorem Zonotope.aux_pattern1 {h : ℕ} (a : Fin h → ℝ)
    (hP : ∀ p n : Fin h, 0 < a p → a n < 0 → ¬ p < n) :
    ∃ k : ℕ, k ≤ h ∧ (∀ j : Fin h, j.val < k → a j ≤ 0) ∧
      (∀ j : Fin h, k ≤ j.val → 0 ≤ a j) := by -- --- PROOF ---
  classical
  -- `k` is the first index holding a positive value, or `h`
  have hex : ∃ m : ℕ, m = h ∨ ∃ p : Fin h, p.val = m ∧ 0 < a p := ⟨h, Or.inl rfl⟩
  refine ⟨Nat.find hex, Nat.find_min' hex (Or.inl rfl), fun j hj => ?_, fun j hj => ?_⟩
  · -- before it nothing is positive
    have := Nat.find_min hex hj
    push Not at this
    exact this.2 j rfl
  · -- after it nothing is negative, else the positive at `k` precedes it
    by_contra hneg
    have hneg' : a j < 0 := not_le.mp hneg
    rcases Nat.find_spec hex with hk | ⟨p, hp, hap⟩
    · omega
    · have hlt : p < j := by
        rcases lt_or_eq_of_le (show p.val ≤ j.val by omega) with h1 | h1
        · exact h1
        · have : p = j := Fin.ext h1
          rw [this] at hap; linarith
      exact hP p j hap hneg' hlt

/-- The sign pattern along sorted generators, either way round. -/
theorem Zonotope.aux_pattern {h : ℕ} (a : Fin h → ℝ)
    (hno : ∀ i j l : Fin h, i < j → j < l →
      ¬(0 < a i ∧ a j < 0 ∧ 0 < a l) ∧ ¬(a i < 0 ∧ 0 < a j ∧ a l < 0)) :
    ∃ k : ℕ, k ≤ h ∧
      ((∀ j : Fin h, j.val < k → 0 ≤ a j) ∧ (∀ j : Fin h, k ≤ j.val → a j ≤ 0) ∨
        (∀ j : Fin h, j.val < k → a j ≤ 0) ∧
          (∀ j : Fin h, k ≤ j.val → 0 ≤ a j)) := by -- --- PROOF ---
  classical
  by_cases hP : ∀ p n : Fin h, 0 < a p → a n < 0 → ¬ p < n
  · -- no positive before a negative
    obtain ⟨k, hk, h1, h2⟩ := Zonotope.aux_pattern1 a hP
    exact ⟨k, hk, Or.inr ⟨h1, h2⟩⟩
  by_cases hN : ∀ n p : Fin h, a n < 0 → 0 < a p → ¬ n < p
  · -- no negative before a positive: the same for `-a`
    obtain ⟨k, hk, h1, h2⟩ := Zonotope.aux_pattern1 (fun j => -a j)
      (fun p n hp hn => hN p n (by simpa using hp) (by simpa using hn))
    exact ⟨k, hk, Or.inl ⟨fun j hj => by simpa using h1 j hj, fun j hj => by simpa using h2 j hj⟩⟩
  -- both orders occur: a `+ - +` or `- + -` triple
  exfalso
  push Not at hP hN
  obtain ⟨p1, n1, hp1, hn1, h1⟩ := hP
  obtain ⟨n2, p2, hn2, hp2, h2⟩ := hN
  by_cases hc : n1 < p2
  · exact (hno p1 n1 p2 h1 hc).1 ⟨hp1, hn1, hp2⟩
  · have : p2 < n1 := by
      rcases lt_or_eq_of_le (not_lt.mp hc) with h3 | h3
      · exact h3
      · rw [h3] at hp2; linarith
    exact (hno n2 p2 n1 h2 this).2 ⟨hn2, hp2, hn1⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.construct_subset_walk (Z : Zonotope (Vec ℝ 2))
    (h1 : ∀ j, 0 ≤ Z.G j 1 ∧ (0 < Z.G j 1 ∨ 0 ≤ Z.G j 0))
    (h2 : ∀ i j : Fin Z.h, i < j → 0 ≤ Z.G i 0 * Z.G j 1 - Z.G i 1 * Z.G j 0) :
    Z.construct ⊆ convexHull ℝ (Set.range Z.walk) := by -- --- PROOF ---
  intro x hx
  by_contra hnot
  -- separate `x` from the hull by a functional `f`
  obtain ⟨f, u, hfx, hfb⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _)
    (((Set.finite_range Z.walk).isCompact_convexHull ℝ).isClosed) hnot
  obtain ⟨β, hβ, rfl⟩ := hx
  -- `f` in coordinates
  set p : ℝ := f (Pi.single 0 1) with hp
  set q : ℝ := f (Pi.single 1 1) with hq
  have hf : ∀ v : Vec ℝ 2, f v = p * v 0 + q * v 1 := fun v => by
    have hv : v = v 0 • (Pi.single 0 1 : Vec ℝ 2) + v 1 • (Pi.single 1 1 : Vec ℝ 2) := by
      ext i; fin_cases i <;> simp
    have := congrArg f hv
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
    rw [this, hp, hq]; ring
  set a : Fin Z.h → ℝ := fun j => p * Z.G j 0 + q * Z.G j 1 with ha
  -- the signs of `f` along the generators change at most once
  have hno : ∀ i j l : Fin Z.h, i < j → j < l →
      ¬(0 < a i ∧ a j < 0 ∧ 0 < a l) ∧ ¬(a i < 0 ∧ 0 < a j ∧ a l < 0) := fun i j l hij hjl =>
    Zonotope.aux_noalt p q (Z.G i) (Z.G j) (Z.G l) (h1 i) (h1 j) (h1 l) (h2 i j hij) (h2 j l hjl)
      (h2 i l (hij.trans hjl))
  obtain ⟨k, hk, hcase⟩ := Zonotope.aux_pattern a hno
  -- `f` of a corner, and of the point
  have hcorner : ∀ σ : Fin Z.h → Bool, f (Z.corner σ) = f Z.c
      + ∑ j, (if σ j then (1 : ℝ) else -1) * a j := fun σ => by
    rw [Zonotope.corner, map_add, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, hf (Z.G j)]
  have hpoint : f (Z.c + ∑ j, β j • Z.G j) = f Z.c + ∑ j, β j * a j := by
    rw [map_add, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, hf (Z.G j)]
  have hbound : ∀ σ : Fin Z.h → Bool, (∀ j, (if σ j then (1 : ℝ) else -1) * a j ≤ β j * a j) →
      f (Z.corner σ) ≤ f (Z.c + ∑ j, β j • Z.G j) := fun σ hσ => by
    rw [hcorner, hpoint]
    exact add_le_add le_rfl (Finset.sum_le_sum fun j _ => hσ j)
  have hkl : k < Z.h + 1 := Nat.lt_succ_of_le hk
  rcases hcase with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · -- `+` on the generators from `k` on: the second block's corner
    have hmem : Z.corner (fun j => !decide (j.val < k)) ∈ Set.range Z.walk :=
      ⟨Fin.natAdd _ ⟨k, hkl⟩, by simp only [Zonotope.walk, Fin.append_right]⟩
    have := hbound (fun j => !decide (j.val < k)) (fun j => by
      have hb := abs_le.mp (hβ j)
      by_cases hj : j.val < k
      · have := hA j hj
        simp only [hj, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
        nlinarith [hb.1]
      · have := hB j (not_lt.mp hj)
        simp only [hj, decide_false, Bool.not_false, if_true]
        nlinarith [hb.2])
    have := hfb _ (subset_convexHull ℝ _ hmem)
    linarith
  · -- `+` on the generators before `k`: the first block's corner
    have hmem : Z.corner (fun j => decide (j.val < k)) ∈ Set.range Z.walk :=
      ⟨Fin.castAdd _ ⟨k, hkl⟩, by simp only [Zonotope.walk, Fin.append_left]⟩
    have := hbound (fun j => decide (j.val < k)) (fun j => by
      have hb := abs_le.mp (hβ j)
      by_cases hj : j.val < k
      · have := hA j hj
        simp only [hj, decide_true, if_true]
        nlinarith [hb.2]
      · have := hB j (not_lt.mp hj)
        simp only [hj, decide_false, Bool.false_eq_true, if_false]
        nlinarith [hb.1])
    have := hfb _ (subset_convexHull ℝ _ hmem)
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
