import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyExact

/-!
# `evalPolyReal` on a `List.ofFn` is the monomial sum

Horner over a coefficient list, read at coefficients indexed by degree: the `t`
each step factors out is exactly the extra degree every remaining term carries,
so the recursion collapses to `∑ j, c j * t ^ j`.

Which is the form a caller states its own polynomial in — an activation layer
holds a coefficient *function* per neuron and hands `evalPoly` a list — so the
two spellings have to meet somewhere, and this is the only place they do.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.evalPolyReal_ofFn (t : ℝ) : ∀ {k : ℕ} (c : Fin k → ℝ),
    PolyZonotope.evalPolyReal (List.ofFn c) t = ∑ j, c j * t ^ (j : ℕ) := by
  intro k
  induction k with
  | zero => intro c; simp [PolyZonotope.evalPolyReal]
  | succ k ih =>
    intro c
    rw [List.ofFn_succ, PolyZonotope.evalPolyReal, ih, Fin.sum_univ_succ, Finset.mul_sum]
    -- the `t` Horner factors out is the extra degree each remaining term carries
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => by ring)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
