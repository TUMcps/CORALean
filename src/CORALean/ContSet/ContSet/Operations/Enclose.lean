import CORALean.ContSet.ContSet.ContSet

/-!
# CORA's `enclose`: a set enclosing `S ∪ (M S + S₂)`

CORA's `enclose(S, M, S₂)` returns the convex hull of `S` and `M S ⊕ S₂`. Written over the
classes, as the `linComb` of `S` and `mtimes M S` plus `S₂`: nothing here is specific to a
representation, and a representation that has `LinComb`, `Mtimes` and `Plus` gets it. The hull
is a `linComb`, which is the hull only where both operands are convex.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `enclose`: the hull of `S` and `M S ⊕ S₂`, as `linComb S (M S + S₂)`. -/
def ContSet.enclose (s : S n) (M : Mat 𝕋 n n) (s₂ : S n) : S n :=
  let ms := Mtimes.mtimes M s
  let sum := Plus.plus ms s₂
  LinComb.linComb s sum

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
