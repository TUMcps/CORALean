module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import Mathlib.Algebra.BigOperators.Pi

@[expose] public section

/-!
# Membership in a polynomial zonotope, coordinatewise

`construct` is stated over any real module; at `Vec ℝ n` an operation reasons
one coordinate at a time, and this is the reading it uses. The scalar sits on
the right of each generator entry, as it does for `Zonotope`.

The float layer inherits it — its `mem_nominalSet_iff` is this theorem at the
nominal polynomial zonotope.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.mem_construct_iff {n : ℕ} {pZ : PolyZonotope (Vec ℝ n)}
    {x : Vec ℝ n} : -- --- STMT ---
    x ∈ pZ.construct ↔
      ∃ a : Fin pZ.p → ℝ, ∃ β : Fin pZ.q → ℝ, (∀ k, |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1)
        ∧ ∀ i, x i = pZ.c i + (∑ l, pZ.G l i * PolyZonotope.monomial pZ.E a l)
              + ∑ j, pZ.GI j i * β j := by -- --- PROOF ---
  -- one coordinate of the defining equation, both generator blocks transposed
  have key : ∀ (a : Fin pZ.p → ℝ) (β : Fin pZ.q → ℝ) (i : Fin n),
      (pZ.c + ∑ l, PolyZonotope.monomial pZ.E a l • pZ.G l + ∑ j, β j • pZ.GI j) i
        = pZ.c i + (∑ l, pZ.G l i * PolyZonotope.monomial pZ.E a l)
            + ∑ j, pZ.GI j i * β j := by
    intro a β i
    rw [Pi.add_apply, Entrywise.add_sum_smul_apply, Finset.sum_apply]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => by
      rw [Pi.smul_apply, smul_eq_mul, mul_comm])
  constructor
  · rintro ⟨a, β, ha, hβ, rfl⟩
    exact ⟨a, β, ha, hβ, key a β⟩
  · rintro ⟨a, β, ha, hβ, hx⟩
    exact ⟨a, β, ha, hβ, funext fun i => (hx i).trans (key a β i).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
