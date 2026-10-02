import CORALean.ContSet.Capsule.Real.Theorems.ConstructEqEmpty
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Order.Lattice

/-!
# When a capsule is full-dimensional

A capsule `{c + t g | t ∈ [-1, 1]} ⊕ ball(0, r)` has an interior point iff it is nonempty
(`0 ≤ r`; a negative radius denotes `∅`) and either the ball is thick (`0 < r`) or the space is
too small for a thin capsule to miss it: `n = 0` (the whole one-point space) or `n = 1` with
`g ≠ 0` (a non-degenerate segment is an interval of the line).

CORA's `@capsule/isFullDim.m` answers `~isempty(C.r) && C.r > 0`, which misses exactly the two
thin cases: `n = 1`, `r = 0`, `g ≠ 0` and `n = 0`, `r = 0`.

For `r = 0` the set is the segment itself. An interior point `x` has `x + ε eᵢ` in the set for
every axis `i`, so `ε eᵢ` is a multiple of `g`: `g` is nonzero in axis `i` and zero in all others,
which allows one axis only.

Stated at `construct`, which is what `ContSet.IsFullDim` unfolds to: the `ContSet` instance is
declared after the theorems.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


/-- A thin capsule is its segment. -/
private lemma Capsule.mem_construct_of_r_eq_zero {C : Capsule n} (hr : C.r = 0) {x : Vec ℝ n} :
    x ∈ C.construct ↔ ∃ t ∈ Set.Icc (-1 : ℝ) 1, ∀ i, x i = C.c i + t * C.g i := by -- --- PROOF ---
  unfold Capsule.construct
  simp only [Set.mem_setOf_eq, hr]
  refine exists_congr fun t => and_congr_right fun _ => ?_
  constructor
  · intro h
    have h0 : Real.sqrt (∑ i, (x i - (C.c i + t * C.g i)) ^ 2) = 0 :=
      le_antisymm h (Real.sqrt_nonneg _)
    have h1 := Real.sqrt_eq_zero'.mp h0
    have h2 : ∑ i, (x i - (C.c i + t * C.g i)) ^ 2 = 0 :=
      le_antisymm h1 (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp h2 i
      (Finset.mem_univ i)
    have := pow_eq_zero_iff (two_ne_zero) |>.mp this
    linarith
  · intro h
    have : ∑ i, (x i - (C.c i + t * C.g i)) ^ 2 = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [h i]; ring
    rw [this]; simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.isFullDim_iff (C : Capsule n) :
    (interior C.construct).Nonempty ↔
      0 < C.r ∨ (0 ≤ C.r ∧ (n = 0 ∨ (n = 1 ∧ C.g ≠ 0))) := by -- --- PROOF ---
  constructor
  · rintro ⟨x, hx⟩
    rcases lt_trichotomy C.r 0 with hr | hr | hr
    · rw [Capsule.construct_eq_empty hr] at hx
      simp at hx
    · right
      refine ⟨hr.ge, ?_⟩
      by_contra hcon
      push Not at hcon
      obtain ⟨hn0, hn1⟩ := hcon
      -- along each axis the capsule contains a point beside `x`
      have key : ∀ i : Fin n, C.g i ≠ 0 ∧ ∀ j, j ≠ i → C.g j = 0 := by
        intro i
        -- a ball about `x` lies in the capsule, so it holds `x` shifted along axis `i`
        obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
        have hmem : x + Pi.single i (ε / 2) ∈ C.construct := by
          apply hball
          rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
            pi_norm_lt_iff hε]
          intro j
          by_cases hji : j = i
          · subst hji; simp only [Pi.single_eq_same, Real.norm_eq_abs]
            rw [abs_of_pos (half_pos hε)]; linarith
          · simp [hji, hε]
        -- both points are on the segment, so their difference is a multiple of `g`
        obtain ⟨s, -, hs⟩ := (Capsule.mem_construct_of_r_eq_zero hr).mp (interior_subset hx)
        obtain ⟨t, -, ht⟩ := (Capsule.mem_construct_of_r_eq_zero hr).mp hmem
        have hd : ∀ j, (Pi.single i (ε / 2) : Vec ℝ n) j = (t - s) * C.g j := by
          intro j
          have := ht j
          have := hs j
          simp only [Pi.add_apply] at *
          linarith
        -- read the multiple off axis `i` (nonzero) and off the other axes (zero)
        refine ⟨fun h0 => ?_, fun j hj => ?_⟩
        · have := hd i
          rw [h0] at this
          simp at this
          linarith
        · have := hd j
          have hts : t - s ≠ 0 := by
            intro h0
            have := hd i
            rw [h0] at this
            simp at this
            linarith
          simp [hj] at this
          rcases this with h | h
          · exact absurd h hts
          · exact h
      -- one axis only, and the capsule has a direction
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · by_cases h0 : n = 0
        · exact hn0 h0
        · have h1 : n = 1 := by omega
          exact (key ⟨0, by omega⟩).1 (by rw [hn1 h1]; rfl)
      · obtain ⟨_, h1⟩ := key ⟨0, by omega⟩
        exact (key ⟨1, by omega⟩).1 (h1 ⟨1, by omega⟩ (by simp [Fin.ext_iff]))
    · exact Or.inl hr
  · rintro (hr | ⟨hr, hn | ⟨hn, hg⟩⟩)
    · -- a thick capsule contains the open ball about the centre
      refine ⟨C.c, mem_interior.mpr ⟨{x | ∑ i, (x i - C.c i) ^ 2 < C.r ^ 2}, ?_, ?_, ?_⟩⟩
      · intro x hx
        refine ⟨0, by simp, ?_⟩
        rw [Real.sqrt_le_iff]
        refine ⟨hr.le, ?_⟩
        simpa using hx.le
      · exact isOpen_lt (continuous_finsetSum _ fun i _ =>
          ((continuous_apply i).sub continuous_const).pow 2) continuous_const
      · simpa using pow_pos hr 2
    · -- `n = 0`: the whole one-point space
      subst hn
      refine ⟨0, ?_⟩
      have : C.construct = Set.univ := by
        ext x
        simp only [Set.mem_univ, iff_true]
        exact ⟨0, by simp, by simpa using hr⟩
      rw [this, interior_univ]; trivial
    · -- `n = 1`: a non-degenerate segment is an interval of the line
      subst hn
      have hg0 : C.g 0 ≠ 0 := fun h => hg (funext fun i => by
        have : i = 0 := Subsingleton.elim _ _
        subst this; simpa using h)
      have hgp : 0 < |C.g 0| := abs_pos.mpr hg0
      refine ⟨C.c, mem_interior.mpr ⟨{x | |x 0 - C.c 0| < |C.g 0|}, ?_, ?_, ?_⟩⟩
      · intro x hx
        refine ⟨(x 0 - C.c 0) / C.g 0, ?_, ?_⟩
        · have : |(x 0 - C.c 0) / C.g 0| ≤ 1 := by
            rw [abs_div, div_le_one hgp]; exact le_of_lt hx
          exact abs_le.mp this
        · have : ∑ i : Fin 1, (x i - (C.c i + (x 0 - C.c 0) / C.g 0 * C.g i)) ^ 2 = 0 := by
            simp
            field_simp
            ring
          rw [this]; simpa using hr
      · exact isOpen_lt (((continuous_apply 0).sub continuous_const).abs) continuous_const
      · simpa using hgp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
