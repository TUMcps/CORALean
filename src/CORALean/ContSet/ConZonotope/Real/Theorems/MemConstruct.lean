import CORALean.ContSet.ConZonotope.Real.ConZonotope

/-!
# Membership in a constrained zonotope, coordinatewise

`construct` is stated over any real module; at `Vec ℝ n` an operation reasons
one coordinate at a time, and this is the reading it uses. The constraint stays
as it is — it lives on the coefficient space, which has coordinates whatever the
generators point into.

The float layer inherits it — its `mem_nominalSet_iff` is this theorem at the
nominal constrained zonotope.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.mem_construct_iff {n : ℕ} {cZ : ConZonotope (Vec ℝ n)} {x : Vec ℝ n} :
    x ∈ cZ.construct ↔ ∃ β : Fin cZ.h → ℝ, (∀ j, |β j| ≤ 1) ∧ β ∈ cZ.P.construct
      ∧ ∀ i, x i = cZ.c i + ∑ j, cZ.G j i * β j := by -- --- PROOF ---
  constructor
  · rintro ⟨β, hβ, hP, rfl⟩
    exact ⟨β, hβ, hP, Entrywise.add_sum_smul_apply cZ.c cZ.G β⟩
  -- back, the pointwise equalities collected into one by `funext`
  · rintro ⟨β, hβ, hP, hx⟩
    exact ⟨β, hβ, hP,
      funext fun i => (hx i).trans (Entrywise.add_sum_smul_apply cZ.c cZ.G β i).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
