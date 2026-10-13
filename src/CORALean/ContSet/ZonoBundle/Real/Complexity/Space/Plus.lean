module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Complexity.Space.Plus
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `ZonoBundle.plus`'s counts

`plus`'s bundle size: every zonotope of one bundle paired with every zonotope
of the other, so the count multiplies rather than adds — the reason it, not
`intersection`, carries this directory's `O`-notation statement, in `PlusBigO.lean`.

The second-order count also comes out cleanly: each paired component is
`Zonotope.plus` of the two it came from, so its own generator count is theirs
added, by `Zonotope.plus_h`. `rfl` against both structure instances.

## `ZonoBundle.plus`'s bundle size is `O(m ^ 2)`

Not a bare arithmetic fact about `m * m`, but one tied to `plus` through a
family of bundles whose sizes grow as `m`. `plus_k` reduces the left side to
that product outright, which `m ^ 2` dominates for every `m`.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [Module ℝ α] in
theorem ZonoBundle.plus_k (zB₁ zB₂ : ZonoBundle α) : (zB₁.plus zB₂).k = zB₁.k * zB₂.k := rfl

omit [Module ℝ α] in
theorem ZonoBundle.plus_Z_h (zB₁ zB₂ : ZonoBundle α) (p : Fin (zB₁.k * zB₂.k)) :
    ((zB₁.plus zB₂).Z p).h =
      (zB₁.Z (finProdFinEquiv.symm p).1).h + (zB₂.Z (finProdFinEquiv.symm p).2).h := rfl


omit [Module ℝ α] in
theorem ZonoBundle.plus_k_isBigO (zB W : ℕ → ZonoBundle α) (hB : ∀ m, (zB m).k = m)
    (hW : ∀ m, (W m).k = m) :
    (fun m : ℕ => (((ZonoBundle.plus (zB m) (W m)).k : ℕ) : ℝ))
      =O[Filter.atTop] fun m : ℕ => ((m : ℝ)) ^ 2 := by -- --- PROOF ---
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  have hk : (ZonoBundle.plus (zB m) (W m)).k = m * m := by
    rw [ZonoBundle.plus_k, hB, hW]
  rw [hk, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  push_cast
  nlinarith [sq_nonneg (m : ℝ)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
