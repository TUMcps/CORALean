import CORALean.ContSet.Conversion.Real.Interval_to_VPolytope
import Mathlib.Order.Nat
import Mathlib.Data.Nat.Find

/-!
# `Interval.exploreBNVisits`

[1, Alg. 2], `EXPLORE BN`, on the ordered box `[0, b₁] × … × [0, bₙ]`: the border vertices
`w` it hands to `FIND SOLUTIONS` (line 8), in the order it reaches them. The paper pops
s-faces off a stack; here each s-face `(p₁, …, p_j, *, …, *)` is a call, its partition's pieces
(line 12) the recursive calls, which visits the same faces depth first. Line 6's maximum `k` is
`Nat.findGreatest`, taken at least `j`: below `j` the condition is the one at `j`. Faces and
vertices are label vectors, `true` for the upper bound; the vertex of `w` is `corner w`.

## References

* [1] C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection
      Problem". INFOCOMP Journal of Computer Science, 8(4):21-27, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- The vertices `w` [1, Alg. 2] visits from the s-face `(p₁, …, p_j, *, …, *)`. -/
noncomputable def Interval.exploreBNVisits (b : Vec ℝ n) (α : ℝ) (j : ℕ) (p : Fin n → Bool) :
    List (Fin n → Bool) :=
  -- `(v₁, …, v_j, b_{j+1}, …, b_k, 0, …, 0)` as labels
  let lab : ℕ → Fin n → Bool := fun k i => if (i : ℕ) < j then p i else decide ((i : ℕ) < k)
  let k := max j (Nat.findGreatest                                           -- 6
    (fun k => ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner (lab k) i ≤ α) n)
  let w := lab k                                                             -- 5, 7
  w :: if hk : k < n then                                                    -- 9
    -- 10-12: the pieces `(v₁, …, v_j, b_{j+1}, …, b_{i-1}, 0, *, …)` of `P(v, v')` but `v'`
    (List.range' j (k - j)).attach.flatMap fun i =>
      Interval.exploreBNVisits b α (i.1 + 1) fun m => if (m : ℕ) = i.1 then false else w m
  else []
termination_by n - j
decreasing_by
  have hi := List.mem_range'_1.mp i.2
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
