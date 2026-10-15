module

public import CORALean.ContSet.HPolytope.Float.Operations.Basic

@[expose] public section

/-!
# `HPolytope.absorbRounding`: the error box folded into the rows

A box is not a halfspace, but its effect on one is a number: the points of `N ⊕ E` satisfy
`A x ≤ b + max_{e ∈ E} A e`. This writes every row that way, rounded up, and each equality
as the two inequalities it stands for, since an equality has no direction to widen in. The
result has no box, so it is an ordinary description of a superset.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.absorbRounding (P : HPolytope 𝕋 (Vec 𝕋 n)) : HPolytope 𝕋 (Vec 𝕋 n) where
  m := P.m + (P.me + P.me)
  A := Fin.append P.A (Fin.append P.Ae fun i j => neg (P.Ae i j))
  b := Fin.append P.bU (Fin.append P.beU P.beLN)
  me := 0
  Ae := fun i => i.elim0
  be := fun i => i.elim0
  I_error := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
