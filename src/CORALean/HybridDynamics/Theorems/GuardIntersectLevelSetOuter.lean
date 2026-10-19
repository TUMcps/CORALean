module

public import CORALean.HybridDynamics.Operations.GuardIntersectLevelSet
public import CORALean.ContSet.Interval.Real.Theorems.OrOuter
public import CORALean.ContSet.LevelSet.Real.Definitions.Contractor

@[expose] public section

/-!
# The box `guardIntersectLevelSet` returns holds the guard intersection

[1, Sec. 3.2], Steps 2-3: a point of a reach set's box on the guard `{x | g(x) = 0}` lies in
the hull, whatever `contract` is, as long as it is a contractor for `g` ([1, Def. 6],
`IsContractor`; `LevelSet.tightenDomainLinear_isContractor` is CORA's `'linear'` one, the
identity the `try` that fails). So `R ∩ guard ⊆ I ∩ guard`, and [1, Prop. 1] or
[1, Prop. 2] on `I` (`guardIntersectSolvable_subset`, `guardIntersectUnsolvable_subset`)
encloses that. Outer.

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- What the start holds, and what any `h R` of the list holds, the fold of hulls holds. -/
theorem Location.aux_mem_foldl_or (h : Real.Interval (Vec ℝ n) → Real.Interval (Vec ℝ n))
    (Rs : List (Real.Interval (Vec ℝ n))) (I : Real.Interval (Vec ℝ n)) {x : Vec ℝ n}
    (hx : x ∈ I.construct ∨ ∃ R ∈ Rs, x ∈ (h R).construct) :
    x ∈ (Rs.foldl (fun I R => I.or (h R)) I).construct := by -- --- PROOF ---
  induction Rs generalizing I with
  | nil =>
    rcases hx with hx | ⟨R, hR, -⟩
    · exact hx
    · exact absurd hR List.not_mem_nil
  | cons R Rs ih =>
    -- the first hull takes `I` or `h R`; the rest of the fold is the induction
    refine ih _ ?_
    rcases hx with hx | ⟨R', hR', hxR'⟩
    · exact Or.inl (Real.Interval.or_outer _ _ (Or.inl hx))
    rcases List.mem_cons.mp hR' with rfl | hR'
    · exact Or.inl (Real.Interval.or_outer _ _ (Or.inr hxR'))
    · exact Or.inr ⟨R', hR', hxR'⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 3.2], Steps 2-3: a point on the guard in one of the boxes `R₀ :: Rs` lies in the
hull of their tightened boxes, and on the guard. -/
theorem Location.guardIntersectLevelSet_outer {g : Vec ℝ n → ℝ}
    {contract : Real.Interval (Vec ℝ n) → Real.Interval (Vec ℝ n)}
    (hc : Real.IsContractor g contract) {R₀ : Real.Interval (Vec ℝ n)}
    {Rs : List (Real.Interval (Vec ℝ n))} {x : Vec ℝ n}
    (hx : ∃ R ∈ R₀ :: Rs, x ∈ R.construct) (hg : g x = 0) : -- --- CONCL ---
    x ∈ (Location.guardIntersectLevelSet contract R₀ Rs).construct ∩
      {x | g x = 0} := by -- --- PROOF ---
  refine ⟨?_, hg⟩
  obtain ⟨R, hR, hxR⟩ := hx
  have hxc : x ∈ (contract R).construct := (hc R).2 x hxR hg
  -- the contractor keeps `x` in the tightened box of its own reach set
  refine Location.aux_mem_foldl_or contract Rs (contract R₀) ?_
  rcases List.mem_cons.mp hR with rfl | hR
  · exact Or.inl hxc
  · exact Or.inr ⟨R, hR, hxc⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
