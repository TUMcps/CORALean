module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# A box cut by a hyperplane

[1, Eq. 2]: the hyperplane `Σᵢ xᵢ = α`; `hyperplane a α` is the scaled `Σᵢ aᵢxᵢ = α` of
[1, Sec. 6.3 (scaling)], `a = 1` the paper's own. [1, Sec. 1]: the vertices of the cut lie on
the edges of the box, perhaps at a vertex; `IsOnEdge` says that of a point — at most one
coordinate strictly between its bounds. [1, Def. 3]: a squashed face `(p₁, …, p_j, *, …, *)`
fixes the first `j` labels, the only s-faces the algorithm forms; `prefixFace j p` is the
set `V(s)` of labels it represents, a label `l` naming the vertex `I.corner l`.

## Inputs
* `a` – normal vector
* `α` – level of the hyperplane

## Output
* the hyperplane with normal `a` at level `α`

## References

* [1] C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection
      Problem". INFOCOMP Journal of Computer Science, 8(4):21-27, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The hyperplane `Σᵢ aᵢ xᵢ = α`. -/
def Interval.hyperplane (a : Vec ℝ n) (α : ℝ) : Set (Vec ℝ n) := {x | ∑ i, a i * x i = α}

/-- On an edge of `I`, perhaps at a vertex: no two coordinates strictly inside. -/
def Interval.IsOnEdge (I : Interval (Vec ℝ n)) (x : Vec ℝ n) : Prop :=
  ∀ i j, i ≠ j → (x i = I.inf i ∨ x i = I.sup i) ∨ (x j = I.inf j ∨ x j = I.sup j)

/-- `V(s)` of the s-face `(p₁, …, p_j, *, …, *)`: the labels agreeing with `p` below `j`. -/
def Interval.prefixFace (j : ℕ) (p : Fin n → Bool) : Set (Fin n → Bool) :=
  {l | ∀ i : Fin n, (i : ℕ) < j → l i = p i}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
