module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalW
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpWApply
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.QuadTermAttained
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.MemMat

@[expose] public section

/-!
# `expIntervalW` attains both of its bounds

[1, Lemma 1], the half the word *exact* stands for: every entry's two bounds are values `W(t)`
really takes on the box, so no smaller interval matrix encloses `W(t)` entrywise. With
`expW_mem_expIntervalW` this is [1, Lemma 1] as stated. The witness is built entry by entry, which
the single-use rearrangement buys: the variables `A i j`, the two diagonal entries, and the `A i k`,
`A k j` of the `k ≠ i, j` sum are pairwise distinct, so each may be sent to whichever corner its own
term wants. The two diagonal entries enter through one factor `[L, H]`, so they move together
(`aux_diag_choice`). Exactness is entrywise, not as a set: the image of the box under `W(t)` is
generally no interval matrix.

## Inputs
* `A` – interval matrix
* `t` – time
* `i` – row index
* `j` – column index

## Hypotheses
* `ht` – time nonzero
* `hA` – box nonempty

## Conclusion
* both bounds of the entry are attained by members of the box

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". In Proc. of the 46th IEEE Conference on Decision and Control (CDC),
      2007, pp. 726-732.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A corner of an interval is in it. -/
theorem aux_corner_mem {lo hi v : ℝ} (h : v = lo ∨ v = hi) (hle : lo ≤ hi) :
    lo ≤ v ∧ v ≤ hi := by
  rcases h with rfl | rfl
  · exact ⟨le_rfl, hle⟩
  · exact ⟨hle, le_rfl⟩

/-- `mulLo` is one of the four corner products, and says which corners. -/
theorem aux_mulLo_corner (a b c d : ℝ) : -- --- CONCL ---
    ∃ y x, (y = a ∨ y = b) ∧ (x = c ∨ x = d) ∧ y * x = Interval.mulLo a b c d := by -- --- PROOF ---
  rcases min_cases (min (a * c) (a * d)) (min (b * c) (b * d)) with ⟨h1, -⟩ | ⟨h1, -⟩
  · rcases min_cases (a * c) (a * d) with ⟨h2, -⟩ | ⟨h2, -⟩
    · exact ⟨a, c, Or.inl rfl, Or.inl rfl, by rw [Interval.mulLo, h1, h2]⟩
    · exact ⟨a, d, Or.inl rfl, Or.inr rfl, by rw [Interval.mulLo, h1, h2]⟩
  · rcases min_cases (b * c) (b * d) with ⟨h2, -⟩ | ⟨h2, -⟩
    · exact ⟨b, c, Or.inr rfl, Or.inl rfl, by rw [Interval.mulLo, h1, h2]⟩
    · exact ⟨b, d, Or.inr rfl, Or.inr rfl, by rw [Interval.mulLo, h1, h2]⟩

/-- The same for `mulHi`. -/
theorem aux_mulHi_corner (a b c d : ℝ) : -- --- CONCL ---
    ∃ y x, (y = a ∨ y = b) ∧ (x = c ∨ x = d) ∧ y * x = Interval.mulHi a b c d := by -- --- PROOF ---
  rcases max_cases (max (a * c) (a * d)) (max (b * c) (b * d)) with ⟨h1, -⟩ | ⟨h1, -⟩
  · rcases max_cases (a * c) (a * d) with ⟨h2, -⟩ | ⟨h2, -⟩
    · exact ⟨a, c, Or.inl rfl, Or.inl rfl, by rw [Interval.mulHi, h1, h2]⟩
    · exact ⟨a, d, Or.inl rfl, Or.inr rfl, by rw [Interval.mulHi, h1, h2]⟩
  · rcases max_cases (b * c) (b * d) with ⟨h2, -⟩ | ⟨h2, -⟩
    · exact ⟨b, c, Or.inr rfl, Or.inl rfl, by rw [Interval.mulHi, h1, h2]⟩
    · exact ⟨b, d, Or.inr rfl, Or.inr rfl, by rw [Interval.mulHi, h1, h2]⟩

/-- Either endpoint of the factor `[L, H]` is realised by sending *both* diagonal
entries to the matching endpoint — the one place two variables move together. -/
theorem aux_diag_choice (A : Interval (Mat ℝ n n)) (t : ℝ) (i j : Fin n) {x : ℝ}
    (hx : x = t + t ^ 2 / 2 * (A.inf i i + A.inf j j)
      ∨ x = t + t ^ 2 / 2 * (A.sup i i + A.sup j j))
    (hA : ∀ p q, A.inf p q ≤ A.sup p q) : -- --- CONCL ---
    ∃ u : Fin n → ℝ, (∀ p, A.inf p p ≤ u p ∧ u p ≤ A.sup p p) ∧
      t + t ^ 2 / 2 * (u i + u j) = x := by -- --- PROOF ---
  rcases hx with rfl | rfl
  · exact ⟨fun p => A.inf p p, fun p => ⟨le_rfl, hA p p⟩, rfl⟩
  · exact ⟨fun p => A.sup p p, fun p => ⟨hA p p, le_rfl⟩, rfl⟩

/-- Off the diagonal, any independent choice inside the five families of entries
entry `(i, j)` depends on is realised by one member of the box. -/
theorem aux_expW_offDiag_exists (A : Interval (Mat ℝ n n)) (t : ℝ) {i j : Fin n}
    (hij : ¬ i = j) (hA : ∀ p q, A.inf p q ≤ A.sup p q)
    {y : ℝ} (hy : A.inf i j ≤ y ∧ y ≤ A.sup i j)
    (u : Fin n → ℝ) (hu : ∀ p, A.inf p p ≤ u p ∧ u p ≤ A.sup p p)
    (d : Fin n → ℝ) (hd : ∀ q, A.inf i q ≤ d q ∧ d q ≤ A.sup i q)
    (e : Fin n → ℝ) (he : ∀ p, A.inf p j ≤ e p ∧ e p ≤ A.sup p j) : -- --- CONCL ---
    ∃ M ∈ A.construct, MatExp.expW M t i j
      = y * (t + t ^ 2 / 2 * (u i + u j))
        + t ^ 2 / 2
          * ∑ k ∈ Finset.univ \ ({i, j} : Finset (Fin n)), d k * e k := by -- --- PROOF ---
  -- the five branches are disjoint exactly because `i ≠ j`
  set M : Mat ℝ n n := fun p q =>
    if p = i ∧ q = j then y else if p = q then u p
    else if p = i then d q else if q = j then e p else A.inf p q with hMdef
  have hMij : M i j = y := by simp [hMdef]
  have hMii : M i i = u i := by simp [hMdef, hij]
  have hMjj : M j j = u j := by simp [hMdef, Ne.symm hij]
  refine ⟨M, ?_, ?_⟩
  · -- every branch lands inside the entry it is chosen for
    refine Interval.mem_mat_iff.mpr fun p q => ?_
    simp only [hMdef]
    split
    · rename_i h; obtain ⟨rfl, rfl⟩ := h; exact hy
    · split
      · rename_i h; subst h; exact hu p
      · split
        · rename_i h; subst h; exact hd q
        · split
          · rename_i h; subst h; exact he p
          · exact ⟨le_rfl, hA p q⟩
  · rw [MatExp.expW_apply, if_neg hij, hMij, hMii, hMjj]
    refine congrArg (fun z => y * (t + t ^ 2 / 2 * (u i + u j)) + t ^ 2 / 2 * z) ?_
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [show M i k = d k by simp [hMdef, hk.2.2, Ne.symm hk.2.1],
      show M k j = e k by simp [hMdef, hk.2.1, hk.2.2]]

/-- On the diagonal the same, with `A i i` left to the parabola. -/
theorem aux_expW_diag_exists (A : Interval (Mat ℝ n n)) (t : ℝ) (i : Fin n)
    (hA : ∀ p q, A.inf p q ≤ A.sup p q)
    {a : ℝ} (ha : A.inf i i ≤ a ∧ a ≤ A.sup i i)
    (d : Fin n → ℝ) (hd : ∀ q, A.inf i q ≤ d q ∧ d q ≤ A.sup i q)
    (e : Fin n → ℝ) (he : ∀ p, A.inf p i ≤ e p ∧ e p ≤ A.sup p i) : -- --- CONCL ---
    ∃ M ∈ A.construct, MatExp.expW M t i i
      = MatExp.quadTerm t a
        + t ^ 2 / 2
          * ∑ k ∈ Finset.univ \ ({i, i} : Finset (Fin n)), d k * e k := by -- --- PROOF ---
  set M : Mat ℝ n n := fun p q =>
    if p = i ∧ q = i then a else if p = i then d q
    else if q = i then e p else A.inf p q with hMdef
  have hMii : M i i = a := by simp [hMdef]
  refine ⟨M, ?_, ?_⟩
  · refine Interval.mem_mat_iff.mpr fun p q => ?_
    simp only [hMdef]
    split
    · rename_i h; obtain ⟨rfl, rfl⟩ := h; exact ha
    · split
      · rename_i h; subst h; exact hd q
      · split
        · rename_i h; subst h; exact he p
        · exact ⟨le_rfl, hA p q⟩
  · rw [MatExp.expW_apply, if_pos rfl, hMii]
    refine congrArg (fun z => MatExp.quadTerm t a + t ^ 2 / 2 * z) ?_
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, or_self] at hk
    rw [show M i k = d k by simp [hMdef, hk.2], show M k i = e k by simp [hMdef, hk.2]]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Each entry's two bounds are attained, so [1, Lemma 1] is exact and not
merely sound. `t ≠ 0` and a non-empty box are what the witnesses need. -/
theorem MatExp.expIntervalW_attained (A : Interval (Mat ℝ n n)) {t : ℝ} (ht : t ≠ 0)
    (hA : ∀ p q, A.inf p q ≤ A.sup p q) (i j : Fin n) : -- --- CONCL ---
    (∃ M ∈ A.construct, MatExp.expW M t i j = (MatExp.expIntervalW A t).inf i j) ∧
      (∃ M ∈ A.construct,
        MatExp.expW M t i j = (MatExp.expIntervalW A t).sup i j) := by -- --- PROOF ---
  by_cases hij : i = j
  · -- on the diagonal the parabola's own witness joins the row-column sum's
    subst hij
    constructor
    · obtain ⟨a, ha₁, ha₂, ha₃⟩ := (MatExp.quadTerm_attained (hA i i) ht).1
      choose d e hd he hde using fun k =>
        aux_mulLo_corner (A.inf i k) (A.sup i k) (A.inf k i) (A.sup k i)
      obtain ⟨M, hMmem, hMeq⟩ := aux_expW_diag_exists A t i hA ⟨ha₁, ha₂⟩
        d (fun q => aux_corner_mem (hd q) (hA i q)) e (fun p => aux_corner_mem (he p) (hA p i))
      exact ⟨M, hMmem, by
        rw [hMeq, ha₃, Finset.sum_congr rfl fun k _ => hde k]; simp [MatExp.expIntervalW]⟩
    · -- and again for the upper bound, at the parabola's other extreme
      obtain ⟨a, ha₁, ha₂, ha₃⟩ := (MatExp.quadTerm_attained (hA i i) ht).2
      choose d e hd he hde using fun k =>
        aux_mulHi_corner (A.inf i k) (A.sup i k) (A.inf k i) (A.sup k i)
      obtain ⟨M, hMmem, hMeq⟩ := aux_expW_diag_exists A t i hA ⟨ha₁, ha₂⟩
        d (fun q => aux_corner_mem (hd q) (hA i q)) e (fun p => aux_corner_mem (he p) (hA p i))
      exact ⟨M, hMmem, by
        rw [hMeq, ha₃, Finset.sum_congr rfl fun k _ => hde k]; simp [MatExp.expIntervalW]⟩
  · -- off it the leading factor is a single-use product, so a corner of each
    constructor
    · obtain ⟨y, x, hy, hx, hyx⟩ := aux_mulLo_corner (A.inf i j) (A.sup i j)
        (t + t ^ 2 / 2 * (A.inf i i + A.inf j j)) (t + t ^ 2 / 2 * (A.sup i i + A.sup j j))
      obtain ⟨u, hu, hux⟩ := aux_diag_choice A t i j hx hA
      choose d e hd he hde using fun k =>
        aux_mulLo_corner (A.inf i k) (A.sup i k) (A.inf k j) (A.sup k j)
      obtain ⟨M, hMmem, hMeq⟩ := aux_expW_offDiag_exists A t hij hA
        (aux_corner_mem hy (hA i j)) u hu d (fun q => aux_corner_mem (hd q) (hA i q))
        e (fun p => aux_corner_mem (he p) (hA p j))
      exact ⟨M, hMmem, by
        rw [hMeq, hux, hyx, Finset.sum_congr rfl fun k _ => hde k]
        simp [MatExp.expIntervalW, hij]⟩
    · -- the upper bound the same way, at the greatest corner product instead
      obtain ⟨y, x, hy, hx, hyx⟩ := aux_mulHi_corner (A.inf i j) (A.sup i j)
        (t + t ^ 2 / 2 * (A.inf i i + A.inf j j)) (t + t ^ 2 / 2 * (A.sup i i + A.sup j j))
      obtain ⟨u, hu, hux⟩ := aux_diag_choice A t i j hx hA
      choose d e hd he hde using fun k =>
        aux_mulHi_corner (A.inf i k) (A.sup i k) (A.inf k j) (A.sup k j)
      obtain ⟨M, hMmem, hMeq⟩ := aux_expW_offDiag_exists A t hij hA
        (aux_corner_mem hy (hA i j)) u hu d (fun q => aux_corner_mem (hd q) (hA i q))
        e (fun p => aux_corner_mem (he p) (hA p j))
      exact ⟨M, hMmem, by
        rw [hMeq, hux, hyx, Finset.sum_congr rfl fun k _ => hde k]
        simp [MatExp.expIntervalW, hij]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
