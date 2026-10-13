module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# A generator sum with one term replaced

Splitting a zonotope changes one coefficient and one generator and nothing
else, so every sum on either side of a split is this one: the `j`-th term
written out, plus a reach the split never touches.

Stated with both replacements at once, because `Function.update_eq_self` puts
back whichever of the two is not replaced — so the original sum, each half's,
and the overlap's are all this statement at different arguments, and the shared
`∑ k ∈ univ.erase j` is what lets them be compared at all.

A file of its own rather than a helper, `SplitUnion` and `SplitIntersection`
both reading their sums off it.

Over any real module, nothing here touching a coordinate.
-/

-- Authors:       Claude Opus 5
-- Written:       11-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A generator sum with the `j`-th coefficient and the `j`-th generator both
replaced: that term written out, and everything off `j` untouched. -/
theorem Zonotope.sum_smul_update (β : Fin h → ℝ) (G : Fin h → α) (j : Fin h)
    (t : ℝ) (a : α) :
    ∑ k, Function.update β j t k • Function.update G j a k
      = t • a + ∑ k ∈ Finset.univ.erase j, β k • G k := by -- --- PROOF ---
  have hoff : ∀ k ∈ Finset.univ.erase j,
      Function.update β j t k • Function.update G j a k = β k • G k := fun k hk => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk),
      Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [← Finset.add_sum_erase Finset.univ
    (fun k => Function.update β j t k • Function.update G j a k) (Finset.mem_univ j),
    Finset.sum_congr rfl hoff]
  simp only [Function.update_self]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
