import CORALean.ContSet.Taylm.Real.Operations.BernsteinDegree

/-!
# The Bernstein degree bounds every exponent

`n = max(max(E))` [1] is at least every exponent of every variable in every term: what the
one-variable expansion `pow_eq_sum_bernsteinEntry` asks of its degree.

## References

* [1] `global/functions/helper/sets/contSet/polyZonotope/poly2bernstein.m`, CORA (Sep. 2025).
      No paper behind the rule was confirmed.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.le_bernsteinDegree (T : Taylm n) {a : ℝ × (Fin n → ℕ)} (ha : a ∈ T.terms)
    (k : Fin n) : a.2 k ≤ T.bernsteinDegree := by -- --- PROOF ---
  unfold Taylm.bernsteinDegree
  have key : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.foldr max 0 := by
    intro l
    induction l with
    | nil => intro x hx; simp at hx
    | cons y l ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_max_left _ _
      · exact le_trans (ih x hx) (le_max_right _ _)
  refine key _ _ (List.mem_map.mpr ⟨a, ha, rfl⟩) |> le_trans ?_
  exact Finset.le_sup (f := a.2) (Finset.mem_univ k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
