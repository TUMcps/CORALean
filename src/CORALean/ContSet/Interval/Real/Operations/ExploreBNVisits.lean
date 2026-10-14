module

public import CORALean.ContSet.Conversion.Real.Interval_to_VPolytope
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.Find

@[expose] public section

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
  -- 5. `w ← (v₁, …, v_j, 0, …, 0)`, and 7. `w_i ← b_i` for `j < i ≤ k`, as labels
  let lab : ℕ → Fin n → Bool := fun k i => if (i : ℕ) < j then p i else decide ((i : ℕ) < k)
  -- 6. the maximum `k ≤ n` with `∑_{i ≤ j} v_i + ∑_{j < i ≤ k} b_i ≤ α`
  let k := max j (Nat.findGreatest
    (fun k => ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner (lab k) i ≤ α) n)
  -- 8. `w` is handed to `FIND SOLUTIONS` (the head of the list)
  let w := lab k
  -- 9. if `k < n`, a partition is needed
  w :: if hk : k < n then
    -- 10. lines 10-12: explore every piece `z ∈ P(v, v') \ {v'}` (Lemma 6.2), `v'` as printed
    (List.range' j (k - j)).attach.flatMap fun i =>
      Interval.exploreBNVisits b α (i.1 + 1) fun m => if (m : ℕ) = i.1 then false else w m
  else []
termination_by n - j
decreasing_by
  have hi := List.mem_range'_1.mp i.2
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
