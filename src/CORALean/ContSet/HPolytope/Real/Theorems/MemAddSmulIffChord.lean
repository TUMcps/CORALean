module

public import CORALean.ContSet.HPolytope.Real.Operations.ChordHigh
public import CORALean.ContSet.HPolytope.Real.Operations.ChordLow
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.List.MinMax

@[expose] public section

/-!
# The Boundary Oracle's segment is exactly the chord

`[1, Eq. 1]`: from a point `x` of the open polytope, the line `x + t d` stays in `A x ≤ b`
exactly for `t ∈ [t̲, t̄]`, with `t̲ = max_{tᵢ<0} tᵢ` and `t̄ = min_{tᵢ>0} tᵢ` — the paper's "can be
written explicitly". An absent end (`none`) is no constraint on that side. The strict interior
is what the formula needs: from a boundary point a row with `tᵢ = 0` and `(aᵢ, d) > 0` is
dropped from the minimum although it binds at once.

## References

* [1] B. T. Polyak and E. N. Gryazina. "Billiard walk - a new sampling algorithm for control
      and optimization". In Proc. of the 19th IFAC World Congress, Cape Town, South Africa,
      IFAC Proceedings Volumes 47(3), pp. 6123-6128, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_add_smul_iff_chord (P : HPolytope α) (x d : α)
    (hx : ∀ i, P.A i x < P.b i) (t : ℝ) : -- --- STMT ---
    (∀ i, P.A i (x + t • d) ≤ P.b i) ↔
      (∀ s, P.chordLow x d = some s → s ≤ t) ∧
        (∀ s, P.chordHigh x d = some s → t ≤ s) := by -- --- PROOF ---
  -- the row `i` after moving by `t`, and the sign of `tᵢ` against that of `(aᵢ, d)`
  have hlin : ∀ i, P.A i (x + t • d) = P.A i x + t * P.A i d := by
    intro i; simp
  have hpos : ∀ i, 0 < P.hitTime x d i ↔ 0 < P.A i d := by
    intro i; unfold HPolytope.hitTime
    rw [div_pos_iff]
    constructor
    · intro h
      rcases h with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exfalso; linarith [hx i]
    · intro h; exact Or.inl ⟨by linarith [hx i], h⟩
  have hneg : ∀ i, P.hitTime x d i < 0 ↔ P.A i d < 0 := by
    intro i; unfold HPolytope.hitTime
    rw [div_neg_iff]
    constructor
    · intro h
      rcases h with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exfalso; linarith [hx i]
    · intro h; exact Or.inl ⟨by linarith [hx i], h⟩
  -- what the two argmin/argmax searches return
  have hhigh : ∀ i, P.chordHighIndex x d = some i →
      0 < P.hitTime x d i ∧ ∀ j, 0 < P.hitTime x d j → P.hitTime x d i ≤ P.hitTime x d j := by
    intro i hi
    have hmem := List.argmin_mem hi
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hmem
    refine ⟨hmem, fun j hj => List.le_of_mem_argmin ?_ hi⟩
    simpa using hj
  -- the same for the backward search
  have hlow : ∀ i, P.chordLowIndex x d = some i →
      P.hitTime x d i < 0 ∧ ∀ j, P.hitTime x d j < 0 → P.hitTime x d j ≤ P.hitTime x d i := by
    intro i hi
    have hmem := List.argmax_mem hi
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hmem
    refine ⟨hmem, fun j hj => List.le_of_mem_argmax ?_ hi⟩
    simpa using hj
  -- an empty search means no row has that sign
  have hhigh0 : P.chordHighIndex x d = none → ∀ j, ¬ 0 < P.hitTime x d j := by
    intro h j hj
    have h2 := List.argmin_eq_none.mp h
    have : j ∈ (List.finRange P.m).filter fun i => decide (0 < P.hitTime x d i) := by simpa using hj
    simp [h2] at this
  have hlow0 : P.chordLowIndex x d = none → ∀ j, ¬ P.hitTime x d j < 0 := by
    intro h j hj
    have h2 := List.argmax_eq_none.mp h
    have : j ∈ (List.finRange P.m).filter fun i => decide (P.hitTime x d i < 0) := by simpa using hj
    simp [h2] at this
  -- the two directions of the equivalence
  constructor
  · -- a point of the polytope on the line lies between the two extremes
    intro hmem
    constructor
    · intro s hs
      obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hs
      have hneg' := (hneg i).mp (hlow i hi).1
      have := hmem i
      rw [hlin] at this
      unfold HPolytope.hitTime
      rw [div_le_iff_of_neg hneg']
      linarith
    · intro s hs
      obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hs
      have hpos' := (hpos i).mp (hhigh i hi).1
      have := hmem i
      rw [hlin] at this
      unfold HPolytope.hitTime
      rw [le_div_iff₀ hpos']
      linarith
  · -- between the extremes, every row holds
    rintro ⟨hlo, hhi⟩ i
    rw [hlin]
    rcases lt_trichotomy (P.A i d) 0 with h | h | h
    · -- a backward row: `t̲ ≥ tᵢ` bounds `t` from below
      cases hc : P.chordLowIndex x d with
      | none => exact absurd ((hneg i).mpr h) (hlow0 hc i)
      | some k =>
        have h1 := hlo (P.hitTime x d k) (by simp [HPolytope.chordLow, hc])
        have h2 := (hlow k hc).2 i ((hneg i).mpr h)
        unfold HPolytope.hitTime at h1 h2
        have h3 : (P.b i - P.A i x) / P.A i d ≤ t := h2.trans h1
        rw [div_le_iff_of_neg h] at h3
        linarith
    · rw [h]; linarith [hx i]
    · -- a forward row: `t ≤ t̄ ≤ tᵢ`
      cases hc : P.chordHighIndex x d with
      | none => exact absurd ((hpos i).mpr h) (by simpa using hhigh0 hc i)
      | some k =>
        have h1 := hhi (P.hitTime x d k) (by simp [HPolytope.chordHigh, hc])
        have h2 := (hhigh k hc).2 i ((hpos i).mpr h)
        unfold HPolytope.hitTime at h1 h2
        have h3 : t ≤ (P.b i - P.A i x) / P.A i d := h1.trans h2
        rw [le_div_iff₀ h] at h3
        linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
