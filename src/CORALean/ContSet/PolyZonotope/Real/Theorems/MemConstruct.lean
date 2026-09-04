import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# Membership in a polynomial zonotope, coordinatewise

`construct` is stated over any real module; at `Vec ℝ n` an operation reasons
one coordinate at a time, and this is the reading it uses. The scalar sits on
the right of each generator entry, as it does for `Zonotope`.

The float layer inherits it — its `mem_nominalSet_iff` is this theorem at the
nominal polynomial zonotope.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

theorem PolyZonotope.mem_construct_iff {n : ℕ} {PZ : PolyZonotope (Vec ℝ n)} {x : Vec ℝ n} :
    x ∈ PZ.construct ↔
      ∃ a : Fin PZ.p → ℝ, ∃ β : Fin PZ.q → ℝ, (∀ k, |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1)
        ∧ ∀ i, x i = PZ.c i + (∑ l, PZ.G l i * PolyZonotope.monomial PZ.E a l)
              + ∑ j, PZ.GI j i * β j := by
  -- one coordinate of the defining equation, both generator blocks transposed
  have key : ∀ (a : Fin PZ.p → ℝ) (β : Fin PZ.q → ℝ) (i : Fin n),
      (PZ.c + ∑ l, PolyZonotope.monomial PZ.E a l • PZ.G l + ∑ j, β j • PZ.GI j) i
        = PZ.c i + (∑ l, PZ.G l i * PolyZonotope.monomial PZ.E a l)
            + ∑ j, PZ.GI j i * β j := by
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
