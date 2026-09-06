import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# Membership in a constrained polynomial zonotope, coordinatewise

`construct` is stated over any real module; at `Vec ℝ n` an operation reasons
one coordinate at a time, and this is the reading it uses. The scalar sits on
the right of each generator entry, as it does for `PolyZonotope`, and the
constraint passes through untouched — it is over the factors, not over the
ambient type.

The float layer inherits it — its `mem_nominalSet_iff` is this theorem at the
nominal set.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.mem_construct_iff {n : ℕ} {C : ConPolyZono (Vec ℝ n)} {x : Vec ℝ n} :
    x ∈ C.construct ↔
      ∃ a : Fin C.p → ℝ, ∃ β : Fin C.q → ℝ, (∀ k, |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1)
        ∧ C.satisfies a
        ∧ ∀ i, x i = C.c i + (∑ l, C.G l i * PolyZonotope.monomial C.E a l)
              + ∑ j, C.GI j i * β j := by
  -- one coordinate of the defining equation, both generator blocks transposed
  have key : ∀ (a : Fin C.p → ℝ) (β : Fin C.q → ℝ) (i : Fin n),
      (C.c + ∑ l, PolyZonotope.monomial C.E a l • C.G l + ∑ j, β j • C.GI j) i
        = C.c i + (∑ l, C.G l i * PolyZonotope.monomial C.E a l)
            + ∑ j, C.GI j i * β j := by
    intro a β i
    rw [Pi.add_apply, Entrywise.add_sum_smul_apply, Finset.sum_apply]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => by
      rw [Pi.smul_apply, smul_eq_mul, mul_comm])
  constructor
  · rintro ⟨a, β, ha, hβ, hsat, rfl⟩
    exact ⟨a, β, ha, hβ, hsat, key a β⟩
  · rintro ⟨a, β, ha, hβ, hsat, hx⟩
    exact ⟨a, β, ha, hβ, hsat, funext fun i => (hx i).trans (key a β i).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
