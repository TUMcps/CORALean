module

public import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMap
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `ConPolyZono.quadMap`'s counts

`quadMap` is `quadMapDep` run on `dependent`: the factor and dependent-generator
counts are `dependent`'s own, `quadMapDep`'s square then landing on that count
rather than the operand's, and the independent block empties — the constraint
count `m` and the constraint-generator count `s` both carry straight through,
since the constraint system reads none of the enclosing polynomial zonotope.
`rfl` by unfolding `quadMapDep` and `dependent` rather than restating either.

## `ConPolyZono.quadMap`'s dependent-generator count is `O(m ^ 2)`

Not a bare arithmetic fact about `(m+1)*(m+1)`, but one tied to `quadMap`
through a family of sets whose combined dependent-and-independent count grows
as `m`. `quadMap_h` reduces the left side to that product, which `4 * m ^ 2`
dominates for every `m ≥ 1`.

`Asymptotics.IsBigO.of_bound` closes it: it asks for domination by a fixed
constant `∀ᶠ x in l`, which the whole range `m ≥ 1` clears with room to spare.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.quadMap_p (Q : Fin k → Mat ℝ n n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.quadMap Q cPZ).p = cPZ.p + cPZ.q := rfl

theorem ConPolyZono.quadMap_h (Q : Fin k → Mat ℝ n n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.quadMap Q cPZ).h = (cPZ.h + cPZ.q + 1) * (cPZ.h + cPZ.q + 1) := rfl

theorem ConPolyZono.quadMap_q (Q : Fin k → Mat ℝ n n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.quadMap Q cPZ).q = 0 := rfl

theorem ConPolyZono.quadMap_m (Q : Fin k → Mat ℝ n n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.quadMap Q cPZ).m = cPZ.m := rfl

theorem ConPolyZono.quadMap_s (Q : Fin k → Mat ℝ n n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.quadMap Q cPZ).s = cPZ.s := rfl


theorem ConPolyZono.quadMap_h_isBigO (Q : Fin k → Mat ℝ n n) (cPZ : ℕ → ConPolyZono (Vec ℝ n))
    (hC : ∀ m, (cPZ m).h + (cPZ m).q = m) :
    (fun m : ℕ => (((ConPolyZono.quadMap Q (cPZ m)).h : ℕ) : ℝ))
      =O[Filter.atTop] fun m : ℕ => ((m : ℝ)) ^ 2 := by -- --- PROOF ---
  apply Asymptotics.IsBigO.of_bound 4
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  have hh : (ConPolyZono.quadMap Q (cPZ m)).h = (m + 1) * (m + 1) := by
    rw [ConPolyZono.quadMap_h, hC]
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [hh, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  push_cast
  nlinarith [sq_nonneg ((m : ℝ) - 1)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
