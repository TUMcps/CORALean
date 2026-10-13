module

public import CORALean.Global.Cost
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `Zonotope.exhaustiveSearchCost`

Asserted, not proved, as [1, Prop. 10]'s proof counts it: an exhaustive search for the
best `n` of `p` generators builds the `C(p, n)` parallelotopes of [1, Prop. 8], each
at `O(p)` with respect to the generators — one `Γ⁻¹ g` per generator, `n` fixed — and
then sorts their `C(p, n)` indices `Θ`. The per-parallelotope `p` is the paper's
reading, with its constant in `n` dropped as the paper drops it.

No search here is priced against a Lean definition: `Zonotope.methodC` searches a
filtered shortlist instead, and its cost is [1, Prop. 11]'s, this one at `p = n + κ`.

## [1, Prop. 10]: the exhaustive search is `O(C(p, n) · p)`

The proof's arithmetic, `O(C(p, n) · p) + O(C(p, n) log C(p, n)) = O(C(p, n) · p)`, read
off `exhaustiveSearchCost`: the sort's `log₂ C(p, n)` is at most `p`, since
`C(p, n) ≤ 2ᵖ`, so the sort costs at most `C(p, n)(p + 1)`, and everything at most
`3 C(p, n) p` once `p ≥ 1`. For fixed `n`, as the proposition has it.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid
      Systems Using a Combination of Zonotopes and Polytopes". Nonlinear
      Analysis: Hybrid Systems, 4(2):233-249, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What the exhaustive search of [1, Prop. 10] costs at `n` of `p` generators:
`C(p, n)` parallelotopes at `p` each, and a sort of their `C(p, n)` indices. -/
def Zonotope.exhaustiveSearchCost (n p : ℕ) : Cost :=
  ⟨p.choose n * p⟩ + Cost.sort (p.choose n)


-- =======================================  MAIN THEOREM  ======================================= --

/-- The count itself: at most three times `C(p, n) · p`, from `p = 1` on. -/
theorem Zonotope.exhaustiveSearchCost_ops_le (n p : ℕ) (hp : 1 ≤ p) :
    (Zonotope.exhaustiveSearchCost n p).ops ≤ 3 * (p.choose n * p) := by -- --- PROOF ---
  -- `log₂ C(p, n) ≤ p`, the binomial being at most `2ᵖ`
  have hlog : Nat.log 2 (p.choose n) ≤ p :=
    (Nat.log_mono_right (Nat.choose_le_two_pow p n)).trans (Nat.log_pow (by norm_num) p).le
  simp only [Zonotope.exhaustiveSearchCost, Cost.ops_add, Cost.sort]
  calc p.choose n * p + p.choose n * (Nat.log 2 (p.choose n) + 1)
      ≤ p.choose n * p + p.choose n * (p + p) := by gcongr
    _ = 3 * (p.choose n * p) := by ring

/-- [1, Prop. 10]: for fixed `n`, the exhaustive search over `n` of `p` generators is
`O(C(p, n) · p)` in `p`. -/
theorem Zonotope.exhaustiveSearchCost_isBigO (n : ℕ) :
    (fun p : ℕ => ((Zonotope.exhaustiveSearchCost n p).ops : ℝ))
      =O[Filter.atTop] fun p : ℕ => ((p.choose n * p : ℕ) : ℝ) := by
  apply Asymptotics.IsBigO.of_bound 3
  filter_upwards [Filter.eventually_ge_atTop 1] with p hp
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact_mod_cast Zonotope.exhaustiveSearchCost_ops_le n p hp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
