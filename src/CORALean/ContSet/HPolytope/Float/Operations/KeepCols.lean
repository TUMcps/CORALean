module

public import CORALean.ContSet.HPolytope.Float.HPolytope
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Global.Partition

@[expose] public section

/-!
# `HPolytope.keepCols`: the rows on the kept coordinates, for coefficients in the unit box

What a reduction that boxes some coefficients leaves of a constraint on them: at a partition of
the coordinates into the kept `part.left` and the dropped `part.right`, every row keeps its kept
columns, and what the dropped ones can still add while they stay in `[-1, 1]` is at most the row's
absolute sum over them (`radius`), which is written into the row's slack (#218) rather than its
bound: an inequality reads `Aᵢ x ≤ bᵢ + |b_errorᵢ| + ∑ₗ |Aᵢ,right l|`, and an equality stays an
equality, a slab that much wider. The float counterpart of the exact layer's `keepRows` without
its equality pairs, which the slack makes unnecessary; the error box is not read (a constrained
zonotope's constraint has none) and the result's is the origin.

## Inputs
* `P` – H-polytope
* `part` – split of the coordinates into `q` kept and `r` dropped

## Output
* the rows at `part.left`, each slack grown by its columns at `part.right`, rounded up
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows at `part.left`, each slack grown by its columns at `part.right`, rounded up. -/
def HPolytope.keepCols (P : HPolytope 𝕋 (Vec 𝕋 n)) (part : Split (Fin n) into (Fin q) ⊕ (Fin r)) :
    HPolytope 𝕋 (Vec 𝕋 q) where
  m := P.m
  A := fun i l => P.A i (part.left l)
  b := P.b
  me := P.me
  Ae := fun i l => P.Ae i (part.left l)
  be := P.be
  b_error := fun i =>
    addUp (absolute (P.b_error i)) (radius (fun i l => P.A i (part.right l)) i)
  be_error := fun i =>
    addUp (absolute (P.be_error i)) (radius (fun i l => P.Ae i (part.right l)) i)
  I_error := Interval.origin q

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
