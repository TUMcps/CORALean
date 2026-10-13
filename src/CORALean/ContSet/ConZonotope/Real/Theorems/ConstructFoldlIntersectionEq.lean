module

public import CORALean.ContSet.ConZonotope.Real.Theorems.IntersectionExact

@[expose] public section

/-!
# Folding `intersection` computes the whole intersection

`Fin.foldl m (fun cZ i => cZ.intersection (g i)) init` denotes
`init.construct ∩ ⋂ i, (g i).construct`: `intersection_exact` at each step, and `Fin.foldl_succ`
to peel one `g i` off the family at a time.

Generic in the family `g` rather than built around `Prop. 6`'s own one, since a fold over
`intersection` is what any finite conjunction of constrained-zonotope memberships reduces to, not
only a Minkowski difference by a polytope's vertices.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Folding `intersection` over a family `g` computes the intersection of every set it denotes,
starting from `init`. -/
theorem ConZonotope.construct_foldl_intersection_eq {m : ℕ} (init : ConZonotope (Vec ℝ n))
    (g : Fin m → ConZonotope (Vec ℝ n)) :
    (Fin.foldl m (fun cZ i => cZ.intersection (g i)) init).construct
      = init.construct ∩ ⋂ i, (g i).construct := by -- --- PROOF ---
  induction m generalizing init with
  | zero => simp
  | succ m ih =>
    rw [Fin.foldl_succ, ih (init.intersection (g 0)) (fun i => g i.succ),
      ← ConZonotope.intersection_exact]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    rw [Fin.forall_fin_succ]
    tauto

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
