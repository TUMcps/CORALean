module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import CORALean.Global.Partition

@[expose] public section

/-!
# `PolyZonotope.boxOut`

The last lines of CORA's `outerApprox`: the dependent generators satisfying `removed` leave `G` and
`E`, and the diagonal box `diag(sum(abs(GI_new),2))` of their absolute values, unhalved (`G_red`),
and of the independent generators satisfying `taken` is appended to `GI`, which keeps all its
columns. Which generators are removed is `outerApprox`'s scan; the enclosure holds for any choice
(`BoxOutOuter`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

open CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `pZ` without the `removed` dependent generators, and the box of those and of the `taken`
independent ones appended to the independent block. -/
noncomputable def PolyZonotope.boxOut (pZ : PolyZonotope (Vec ℝ n)) (removed : Fin pZ.h → Prop)
    (taken : Fin pZ.q → Prop) [DecidablePred removed] [DecidablePred taken] :
    PolyZonotope (Vec ℝ n) :=
  -- the radius of the box in each coordinate
  let radius : Fin n → ℝ := fun k =>
    (∑ i, if removed i then |pZ.G i k| else 0) + ∑ j, if taken j then |pZ.GI j k| else 0
  -- the kept generators in order
  let part := Partition.ofPred removed
  { p := pZ.p
    h := Fintype.card {i : Fin pZ.h // ¬ removed i}
    q := pZ.q + n
    c := pZ.c
    G := fun l => pZ.G (part.left l)
    E := fun k l => pZ.E k (part.left l)
    GI := Fin.append pZ.GI (Matrix.diagonal radius) }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
