module

public import CORALean.ContSet.HPolytope.Float.Operations.EqVec
public import CORALean.ContSet.HPolytope.Float.Operations.Restrict

@[expose] public section

/-!
# `HPolytope.dropAligned`: the inequality half of `'aligned'`

CORA's `priv_compact_alignedIneq`: rows with the same normal keep the smallest right-hand side.
A row is deleted when another row with an equal normal (`eqVec`) and no larger slack (`le`) is
certified to have a smaller right-hand side (`ltStrict`), or an equal-or-smaller one and a
smaller index (`le`), so ties keep the first. A comparison that is not certified keeps the row.
The equality rows are untouched.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The inequality rows not dominated by a row with the same normal. -/
def HPolytope.dropAligned (Q : HPolytope 𝕋 (Vec 𝕋 n)) : HPolytope 𝕋 (Vec 𝕋 n) :=
  Q.restrict (fun i => !(List.finRange Q.m).any fun j =>
    (HPolytope.eqVec (Q.A j) (Q.A i) && le (absolute (Q.b_error j)) (absolute (Q.b_error i))) &&
      (ltStrict (Q.b j) (Q.b i) || (decide (j < i) && le (Q.b j) (Q.b i)))) (fun _ => true)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
