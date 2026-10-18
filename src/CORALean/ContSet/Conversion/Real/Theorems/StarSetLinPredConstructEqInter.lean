module

public import CORALean.ContSet.HPolytope.Real.Operations.Ineqs
public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.StarSet.Real.StarSet

@[expose] public section

/-!
# CORA's star-set predicate is a polytope cut by a box

`StarSet.LinPred`, CORA's `C α ≤ d, l ≤ α ≤ u`, denotes the halfspaces `C α ≤ d` of an `HPolytope`,
`HPolytope.ineqs C d` with `C` and `d` the rows read one by one, intersected with the box `[l, u]`
of an `Interval`. So the star set CORA's network layers step through is the general star set whose
predicate is that polytope and that box, stored as CORA stores them.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- `C α ≤ d, l ≤ α ≤ u` is the box `[l, u]` intersected with the polytope `C α ≤ d`. -/
theorem StarSet.LinPred.construct_eq_inter {m : ℕ} (p : StarSet.LinPred m) :
    p.construct = (⟨p.l, p.u⟩ : Interval (Vec ℝ m)).construct ∩
      (HPolytope.ineqs (Matrix.of fun i k => (p.cons.get i).1 k)
        (fun i => (p.cons.get i).2)).construct := by -- --- PROOF ---
  ext α
  -- the box is the interval, and a row of the list is a row of the matrix
  have hrows : (∀ r ∈ p.cons, ∑ k, r.1 k * α k ≤ r.2) ↔
      ∀ i : Fin p.cons.length, ∑ k, (p.cons.get i).1 k * α k ≤ (p.cons.get i).2 :=
    ⟨fun h i => h _ (List.get_mem _ i), fun h r hr => by
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hr
      exact h i⟩
  constructor
  · rintro ⟨hbox, hcons⟩
    exact ⟨hbox, (hrows.mp hcons), fun i => i.elim0⟩
  · rintro ⟨hbox, hcons, -⟩
    exact ⟨hbox, hrows.mpr hcons⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
