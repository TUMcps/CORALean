module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Order.Disjoint
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# [1, Sec. 2.2]: the membership tests a measurement error reduces to

`y ⊕ V ⊆ R` is `y ∈ R ⊖ V` by [1, Sec. 2.2]'s definition of `⊖`. The falsification
`(y ⊕ V) ∩ R = ∅` is `y ∉ R ⊕ (-V)`: some error `v` with `y + v ∈ R` is `y ∈ R - v`. [1,
Sec. 2.2] prints `R ⊕ V`, which is the same only for `V = -V`
(`FalsifyAdd`).

## References

* [1] M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". In Proc. of
      the 10th International Workshop on Applied Verification of Continuous and Hybrid
      Systems (ARCH23), EPiC Series in Computing, vol. 96, pp. 9-33, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 2.2], corrected: `y ⊕ V` misses `R` iff `y ∉ R ⊕ (-V)`. -/
theorem Conform.disjoint_singleton_add_iff {α : Type} [AddCommGroup α] (R V : Set α) (y : α) :
    Disjoint ({y} + V) R ↔ y ∉ R + -V := by -- --- PROOF ---
  rw [Set.disjoint_left]
  constructor
  · rintro h ⟨r, hr, nv, hnv, hy⟩
    refine h ⟨y, rfl, -nv, hnv, ?_⟩ hr
    simp only at hy ⊢
    rw [← hy]
    abel
  · intro h a ⟨b, hb, v, hv, hab⟩ hR
    rw [Set.mem_singleton_iff] at hb
    subst hb
    refine h ⟨a, hR, -v, by simpa using hv, ?_⟩
    simp only at hab ⊢
    rw [← hab]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
