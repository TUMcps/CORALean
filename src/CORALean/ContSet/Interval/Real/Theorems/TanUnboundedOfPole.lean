module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

@[expose] public section

/-!
# The tangent is unbounded both ways on a range around a pole

A pole `p` of the tangent (`cos p = 0`) strictly inside `[a, b]` makes the tangent's values on
the range, its poles left out, unbounded above (just left of `p`) and below (just right of it):
its interval hull is `]-∞, ∞[`, which is what [1, Eq. 14] returns, and through `cot x =
tan(π/2 - x)` what [1, Eq. 15] returns. The values themselves need not be all of `ℝ`: on
`[π/4, 3π/4]` they leave out `(-1, 1)`, as `1/[y]` of [1, Eq. 3] does around `0`.

## Inputs
* `a` – lower end
* `b` – upper end
* `p` – pole of the tangent

## Hypotheses
* `hp` – cosine vanishes at `p`
* `hap` – `a` below `p`
* `hpb` – `p` below `b`

## Conclusion
* the tangent is unbounded above and below on `[a, b]`

## References

* [1] [M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". ARCH16.
      3rd International Workshop on Applied Verification for Continuous and Hybrid Systems,
      2017.](../../../../../../references/2017/althoff-arch-interval-arithmetic.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The tangent takes the value `t` at `arctan t + jπ`, where the cosine does not vanish. -/
private theorem aux_tan_arctan_add (t : ℝ) (j : ℤ) :
    Real.tan (Real.arctan t + j * Real.pi) = t ∧
      Real.cos (Real.arctan t + j * Real.pi) ≠ 0 := by
  refine ⟨by rw [Real.tan_add_int_mul_pi, Real.tan_arctan], ?_⟩
  rw [Real.cos_add_int_mul_pi]
  exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) (Real.cos_arctan_pos t).ne'


-- =======================================  MAIN THEOREM  ======================================= --

/-- A pole strictly inside `[a, b]`: the tangent's values there are unbounded both ways. -/
theorem Interval.tan_unbounded_of_pole {a b p : ℝ} (hp : Real.cos p = 0) (hap : a < p)
    (hpb : p < b) : -- --- CONCL ---
    ¬BddAbove (Real.tan '' (Set.Icc a b ∩ {x | Real.cos x ≠ 0})) ∧
      ¬BddBelow (Real.tan '' (Set.Icc a b ∩ {x | Real.cos x ≠ 0})) := by -- --- PROOF ---
  have hpi := Real.pi_pos
  obtain ⟨j, hj⟩ := Real.cos_eq_zero_iff.1 hp
  constructor
  · -- just left of `p`, at `arctan t + jπ` for large `t`
    rintro ⟨M, hM⟩
    set c := max (a - p + Real.pi / 2) 0
    have hc : c < Real.pi / 2 := max_lt (by linarith) (by linarith)
    set t := max (M + 1) (Real.tan c)
    have hc0 : 0 ≤ c := le_max_right _ _
    have ht : c ≤ Real.arctan t := by
      calc c = Real.arctan (Real.tan c) := (Real.arctan_tan (by linarith) hc).symm
        _ ≤ Real.arctan t := Real.arctan_mono (le_max_right _ _)
    obtain ⟨h1, h2⟩ := aux_tan_arctan_add t j
    have hx := hM ⟨Real.arctan t + j * Real.pi, ⟨⟨?_, ?_⟩, h2⟩, h1⟩
    · linarith [le_max_left (M + 1) (Real.tan c)]
    · have := le_max_left (a - p + Real.pi / 2) 0
      linarith
    · have := Real.arctan_lt_pi_div_two t
      nlinarith
  · -- just right of `p`, at `arctan t + (j + 1)π` for very negative `t`
    rintro ⟨M, hM⟩
    set c := min (b - p - Real.pi / 2) 0
    have hc : -(Real.pi / 2) < c := lt_min (by linarith) (by linarith)
    set t := min (M - 1) (Real.tan c)
    have hc0 : c ≤ 0 := min_le_right _ _
    have ht : Real.arctan t ≤ c := by
      calc Real.arctan t ≤ Real.arctan (Real.tan c) := Real.arctan_mono (min_le_right _ _)
        _ = c := Real.arctan_tan hc (by linarith)
    obtain ⟨h1, h2⟩ := aux_tan_arctan_add t (j + 1)
    have hx := hM ⟨Real.arctan t + ((j + 1 : ℤ) : ℝ) * Real.pi, ⟨⟨?_, ?_⟩, h2⟩, h1⟩
    · linarith [min_le_left (M - 1) (Real.tan c)]
    · have := Real.neg_pi_div_two_lt_arctan t
      push_cast
      nlinarith
    · have := min_le_left (b - p - Real.pi / 2) 0
      push_cast
      nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
