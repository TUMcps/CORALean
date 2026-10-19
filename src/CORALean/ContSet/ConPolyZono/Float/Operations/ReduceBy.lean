module

public import CORALean.ContSet.ConPolyZono.Float.Operations.DropRadius

@[expose] public section

/-!
# `ConPolyZono.reduceBy`, over a floating-point scalar

Split out of `Reduce.lean` (issue #62): read again by `reduceGirard` in this
directory and by `Theorems/ReduceByOuter.lean` and
`Theorems/ReduceGirardOrderLe.lean`, all outside this file.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n d r dI rI : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's reduction at a given pair of partitions, sound for every one of them:
kept dependent generators keep their exponent columns, kept independent ones are
copied, and the rest becomes a box no longer tied to the factors. -/
def ConPolyZono.reduceBy (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (partD : Split (Fin cPZ.h) into (Fin d) ⊕ (Fin r))
    (partI : Split (Fin cPZ.qI) into (Fin dI) ⊕ (Fin rI)) : ConPolyZono 𝕋 (Vec 𝕋 n) where
  p := cPZ.p
  h := d
  qI := dI + n
  c := cPZ.c
  G := fun l => cPZ.G (partD.left l)
  E := fun k l => cPZ.E k (partD.left l)
  GI := Fin.append (fun j => cPZ.GI (partI.left j))
    fun j i => diagonalBlock (cPZ.dropRadius partD partI) i j
  cons := cPZ.cons
  cons_eq := cPZ.cons_eq
  I_error := cPZ.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
