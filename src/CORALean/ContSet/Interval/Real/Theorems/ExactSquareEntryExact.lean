module

public import CORALean.ContSet.Interval.Real.Theorems.ExactSquareOuter
public import CORALean.ContSet.Interval.Real.Theorems.Convex
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-!
# `Interval.exactSquare` is exact entry by entry

For a nonempty box, the entry `(i, j)` of `M * M` takes exactly the values in
`[exactSquare.inf i j, exactSquare.sup i j]` as `M` ranges over the box. Each end is attained
by a matrix built from independent choices (the entries `exactSquare` combines occur once each,
apart from `A i i ^ 2`, whose extremum is a corner or `0`), and the entry is continuous on the
convex box, so everything between is taken.

Exactness is per entry, not as a set: the set of squares is in general no box.

## Inputs
* `A` – interval matrix
* `i` – row index
* `j` – column index

## Hypotheses
* `hA` – `A` has ordered bounds

## Conclusion
* the range of entry `(i, j)` of the square over the box is exactly the computed interval
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A corner is a member of the interval between the ends. -/
private theorem aux_corner_mem {lo hi v : ℝ} (h : v = lo ∨ v = hi) (hle : lo ≤ hi) :
    lo ≤ v ∧ v ≤ hi := by
  rcases h with rfl | rfl
  · exact ⟨le_rfl, hle⟩
  · exact ⟨hle, le_rfl⟩

/-- `mulLo` is the product of two corners. -/
private theorem aux_mulLo_corner (a b c d : ℝ) : -- --- CONCL ---
    ∃ y x, (y = a ∨ y = b) ∧ (x = c ∨ x = d) ∧
      y * x = Interval.mulLo a b c d := by -- --- PROOF ---
  unfold Interval.mulLo
  rcases min_choice (min (a * c) (a * d)) (min (b * c) (b * d)) with h | h <;> rw [h]
  · rcases min_choice (a * c) (a * d) with h' | h' <;> rw [h']
    · exact ⟨a, c, Or.inl rfl, Or.inl rfl, rfl⟩
    · exact ⟨a, d, Or.inl rfl, Or.inr rfl, rfl⟩
  · rcases min_choice (b * c) (b * d) with h' | h' <;> rw [h']
    · exact ⟨b, c, Or.inr rfl, Or.inl rfl, rfl⟩
    · exact ⟨b, d, Or.inr rfl, Or.inr rfl, rfl⟩

/-- `mulHi` is the product of two corners. -/
private theorem aux_mulHi_corner (a b c d : ℝ) : -- --- CONCL ---
    ∃ y x, (y = a ∨ y = b) ∧ (x = c ∨ x = d) ∧
      y * x = Interval.mulHi a b c d := by -- --- PROOF ---
  unfold Interval.mulHi
  rcases max_choice (max (a * c) (a * d)) (max (b * c) (b * d)) with h | h <;> rw [h]
  · rcases max_choice (a * c) (a * d) with h' | h' <;> rw [h']
    · exact ⟨a, c, Or.inl rfl, Or.inl rfl, rfl⟩
    · exact ⟨a, d, Or.inl rfl, Or.inr rfl, rfl⟩
  · rcases max_choice (b * c) (b * d) with h' | h' <;> rw [h']
    · exact ⟨b, c, Or.inr rfl, Or.inl rfl, rfl⟩
    · exact ⟨b, d, Or.inr rfl, Or.inr rfl, rfl⟩

/-- The least value of `x ^ 2` on `[a, b]` is taken. -/
private theorem aux_sq_lo {a b : ℝ} (hab : a ≤ b) : -- --- CONCL ---
    ∃ x, a ≤ x ∧ x ≤ b ∧
      x ^ 2 = if a < 0 ∧ 0 < b then 0 else min (a ^ 2) (b ^ 2) := by -- --- PROOF ---
  by_cases h : a < 0 ∧ 0 < b
  · exact ⟨0, h.1.le, h.2.le, by simp [h]⟩
  · rw [if_neg h]
    rcases min_choice (a ^ 2) (b ^ 2) with h' | h' <;> rw [h']
    · exact ⟨a, le_rfl, hab, rfl⟩
    · exact ⟨b, hab, le_rfl, rfl⟩

/-- The greatest value of `x ^ 2` on `[a, b]` is taken. -/
private theorem aux_sq_hi {a b : ℝ} (hab : a ≤ b) :
    ∃ x, a ≤ x ∧ x ≤ b ∧ x ^ 2 = max (a ^ 2) (b ^ 2) := by
  rcases max_choice (a ^ 2) (b ^ 2) with h' | h' <;> rw [h']
  · exact ⟨a, le_rfl, hab, rfl⟩
  · exact ⟨b, hab, le_rfl, rfl⟩

/-- Off the diagonal the entry `(i, j)` of a square takes the value built from a free choice of
the entries it uses, each once: `M i j`, the two diagonal ones, row `i` and column `j`. -/
private theorem aux_offDiag_witness (A : Interval (Mat ℝ n n)) (hA : ∀ p q, A.inf p q ≤ A.sup p q)
    {i j : Fin n} (hij : i ≠ j) {y u v : ℝ} (hy : A.inf i j ≤ y ∧ y ≤ A.sup i j)
    (hu : A.inf i i ≤ u ∧ u ≤ A.sup i i) (hv : A.inf j j ≤ v ∧ v ≤ A.sup j j)
    {d e : Fin n → ℝ} (hd : ∀ k, A.inf i k ≤ d k ∧ d k ≤ A.sup i k)
    (he : ∀ k, A.inf k j ≤ e k ∧ e k ≤ A.sup k j) : -- --- CONCL ---
    ∃ M ∈ A.construct, (M * M) i j
      = y * (u + v) + ∑ k ∈ Finset.univ \ {i, j}, d k * e k := by -- --- PROOF ---
  classical
  set M : Mat ℝ n n := Matrix.of fun p q =>
    if p = i then (if q = j then y else if q = i then u else d q)
    else if q = j then (if p = j then v else e p) else A.inf p q with hMdef
  refine ⟨M, Interval.mem_mat_iff.mpr fun p q => ?_, ?_⟩
  · -- every entry of `M` is in its interval, case by case
    by_cases hp : p = i
    · by_cases hq : q = j
      · have h : M p q = y := by simp [hMdef, hp, hq]
        rw [h, hp, hq]; exact hy
      · by_cases hq' : q = i
        · have h : M p q = u := by simp [hMdef, hp, hq', hij]
          rw [h, hp, hq']; exact hu
        · have h : M p q = d q := by simp [hMdef, hp, hq, hq']
          rw [h, hp]; exact hd q
    · by_cases hq : q = j
      · by_cases hpj : p = j
        · have h : M p q = v := by simp [hMdef, hq, hpj, Ne.symm hij]
          rw [h, hq, hpj]; exact hv
        · have h : M p q = e p := by simp [hMdef, hp, hq, hpj]
          rw [h, hq]; exact he p
      · have h : M p q = A.inf p q := by simp [hMdef, hp, hq]
        rw [h]; exact ⟨le_rfl, hA p q⟩
  · -- the value: split the sum at `k = i`, `k = j` and read off the entries
    have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
    have hd' : (Finset.univ.erase i).erase j = Finset.univ \ {i, j} := by
      ext k; simp only [Finset.mem_erase, Finset.mem_univ, Finset.mem_sdiff, Finset.mem_insert,
        Finset.mem_singleton]; tauto
    rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ hj, hd']
    have h1 : M i i = u := by simp [hMdef, hij]
    have h2 : M i j = y := by simp [hMdef]
    have h3 : M j j = v := by simp [hMdef, Ne.symm hij]
    have h4 : ∑ k ∈ Finset.univ \ {i, j}, M i k * M k j
        = ∑ k ∈ Finset.univ \ {i, j}, d k * e k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
        true_and, not_or] at hk
      simp [hMdef, hk.1, hk.2]
    rw [h1, h2, h3, h4]; ring

/-- On the diagonal the entry `(i, i)` of a square takes the value built from a free choice of
`M i i`, row `i` and column `i`. -/
private theorem aux_diag_witness (A : Interval (Mat ℝ n n)) (hA : ∀ p q, A.inf p q ≤ A.sup p q)
    {i : Fin n} {a : ℝ} (ha : A.inf i i ≤ a ∧ a ≤ A.sup i i)
    {d e : Fin n → ℝ} (hd : ∀ k, A.inf i k ≤ d k ∧ d k ≤ A.sup i k)
    (he : ∀ k, A.inf k i ≤ e k ∧ e k ≤ A.sup k i) : -- --- CONCL ---
    ∃ M ∈ A.construct, (M * M) i i
      = a ^ 2 + ∑ k ∈ Finset.univ.erase i, d k * e k := by -- --- PROOF ---
  classical
  set M : Mat ℝ n n := Matrix.of fun p q =>
    if p = i then (if q = i then a else d q) else if q = i then e p else A.inf p q with hMdef
  refine ⟨M, Interval.mem_mat_iff.mpr fun p q => ?_, ?_⟩
  · -- every entry of `M` is in its interval, case by case
    by_cases hp : p = i
    · by_cases hq : q = i
      · have h : M p q = a := by simp [hMdef, hp, hq]
        rw [h, hp, hq]; exact ha
      · have h : M p q = d q := by simp [hMdef, hp, hq]
        rw [h, hp]; exact hd q
    · by_cases hq : q = i
      · have h : M p q = e p := by simp [hMdef, hp, hq]
        rw [h, hq]; exact he p
      · have h : M p q = A.inf p q := by simp [hMdef, hp, hq]
        rw [h]; exact ⟨le_rfl, hA p q⟩
  · rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have h1 : M i i = a := by simp [hMdef]
    have h4 : ∑ k ∈ Finset.univ.erase i, M i k * M k i
        = ∑ k ∈ Finset.univ.erase i, d k * e k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≠ i := (Finset.mem_erase.mp hk).1
      simp [hMdef, hk']
    rw [h1, h4]; ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- The entries of the squares of the members of a nonempty box fill the interval
`[exactSquare.inf, exactSquare.sup]` of that entry: both ends are attained, and the members
form a connected set. -/
theorem Interval.exactSquare_entry_exact (A : Interval (Mat ℝ n n))
    (hA : ∀ p q, A.inf p q ≤ A.sup p q) (i j : Fin n) : -- --- CONCL ---
    (fun M : Mat ℝ n n => (M * M) i j) '' A.construct
      = Set.Icc (A.exactSquare.inf i j) (A.exactSquare.sup i j) := by -- --- PROOF ---
  classical
  -- the least value is a value of the entry on the box
  have hlo : ∃ M ∈ A.construct, (M * M) i j = A.exactSquare.inf i j := by
    by_cases hij : i = j
    · subst hij
      obtain ⟨a, ha1, ha2, ha⟩ := aux_sq_lo (hA i i)
      have hk := fun k => aux_mulLo_corner (A.inf i k) (A.sup i k) (A.inf k i) (A.sup k i)
      choose d e hd he hde using hk
      -- the diagonal witness, the square at its extremum and the products at their corners
      obtain ⟨M, hM, hMv⟩ := aux_diag_witness A hA ⟨ha1, ha2⟩
        (fun k => aux_corner_mem (hd k) (hA i k)) (fun k => aux_corner_mem (he k) (hA k i))
      refine ⟨M, hM, ?_⟩
      rw [hMv]
      simp only [Interval.exactSquare, if_true]
      rw [ha]
      exact congrArg _ (Finset.sum_congr rfl fun k _ => hde k)
    · -- off the diagonal: corners of `M i j` and of the diagonal ends, then of the rest
      obtain ⟨y, x, hy, hx, hyx⟩ := aux_mulLo_corner (A.inf i j) (A.sup i j)
        (A.inf i i + A.inf j j) (A.sup i i + A.sup j j)
      have hk := fun k => aux_mulLo_corner (A.inf i k) (A.sup i k) (A.inf k j) (A.sup k j)
      choose d e hd he hde using hk
      obtain ⟨u, v, hu, hv, huv⟩ : ∃ u v, (A.inf i i ≤ u ∧ u ≤ A.sup i i) ∧
          (A.inf j j ≤ v ∧ v ≤ A.sup j j) ∧ u + v = x := by
        rcases hx with rfl | rfl
        · exact ⟨_, _, ⟨le_rfl, hA i i⟩, ⟨le_rfl, hA j j⟩, rfl⟩
        · exact ⟨_, _, ⟨hA i i, le_rfl⟩, ⟨hA j j, le_rfl⟩, rfl⟩
      obtain ⟨M, hM, hMv⟩ := aux_offDiag_witness A hA hij (aux_corner_mem hy (hA i j)) hu hv
        (fun k => aux_corner_mem (hd k) (hA i k)) (fun k => aux_corner_mem (he k) (hA k j))
      refine ⟨M, hM, ?_⟩
      rw [hMv, huv, hyx]
      simp only [Interval.exactSquare, hij, if_false]
      exact congrArg _ (Finset.sum_congr rfl fun k _ => hde k)
  -- the greatest value is a value of the entry on the box
  have hhi : ∃ M ∈ A.construct, (M * M) i j = A.exactSquare.sup i j := by
    by_cases hij : i = j
    · subst hij
      obtain ⟨a, ha1, ha2, ha⟩ := aux_sq_hi (hA i i)
      have hk := fun k => aux_mulHi_corner (A.inf i k) (A.sup i k) (A.inf k i) (A.sup k i)
      choose d e hd he hde using hk
      obtain ⟨M, hM, hMv⟩ := aux_diag_witness A hA ⟨ha1, ha2⟩
        (fun k => aux_corner_mem (hd k) (hA i k)) (fun k => aux_corner_mem (he k) (hA k i))
      refine ⟨M, hM, ?_⟩
      rw [hMv]
      simp only [Interval.exactSquare, if_true]
      rw [ha]
      exact congrArg _ (Finset.sum_congr rfl fun k _ => hde k)
    · -- off the diagonal: corners of `M i j` and of the diagonal ends, then of the rest
      obtain ⟨y, x, hy, hx, hyx⟩ := aux_mulHi_corner (A.inf i j) (A.sup i j)
        (A.inf i i + A.inf j j) (A.sup i i + A.sup j j)
      have hk := fun k => aux_mulHi_corner (A.inf i k) (A.sup i k) (A.inf k j) (A.sup k j)
      choose d e hd he hde using hk
      obtain ⟨u, v, hu, hv, huv⟩ : ∃ u v, (A.inf i i ≤ u ∧ u ≤ A.sup i i) ∧
          (A.inf j j ≤ v ∧ v ≤ A.sup j j) ∧ u + v = x := by
        rcases hx with rfl | rfl
        · exact ⟨_, _, ⟨le_rfl, hA i i⟩, ⟨le_rfl, hA j j⟩, rfl⟩
        · exact ⟨_, _, ⟨hA i i, le_rfl⟩, ⟨hA j j, le_rfl⟩, rfl⟩
      obtain ⟨M, hM, hMv⟩ := aux_offDiag_witness A hA hij (aux_corner_mem hy (hA i j)) hu hv
        (fun k => aux_corner_mem (hd k) (hA i k)) (fun k => aux_corner_mem (he k) (hA k j))
      refine ⟨M, hM, ?_⟩
      rw [hMv, huv, hyx]
      simp only [Interval.exactSquare, hij, if_false]
      exact congrArg _ (Finset.sum_congr rfl fun k _ => hde k)
  -- the entry is continuous on the convex, hence connected, box
  have hcont : Continuous fun M : Mat ℝ n n => (M * M) i j := by
    simp only [Matrix.mul_apply]
    fun_prop
  have hconn : IsPreconnected ((fun M : Mat ℝ n n => (M * M) i j) '' A.construct) :=
    (Convex.isPreconnected (Interval.convex_construct A)).image _ hcont.continuousOn
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨M, hM, rfl⟩
    exact Interval.mem_mat_iff.mp (Interval.exactSquare_outer A hM) i j
  · obtain ⟨M₁, hM₁, h₁⟩ := hlo
    obtain ⟨M₂, hM₂, h₂⟩ := hhi
    exact hconn.Icc_subset ⟨M₁, hM₁, h₁⟩ ⟨M₂, hM₂, h₂⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
