module

public import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHullBlkDiag

@[expose] public section

/-!
# `ConPolyZono.convHullA`

The constraint matrix of [1, Prop. 9]: the linear combination's, once per copy on the
diagonal, and one last row of ones over the weight columns. Entries are copied, with `zero` and
`one` where the exact layer has `0` and `1`, so nothing here rounds.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One copy of `A` per block, and a final row summing the weights. -/
def ConPolyZono.convHullA (a : ℕ) {m q : ℕ} (A : Mat 𝕋 m q) : Mat 𝕋 (a * m + 1) (a * q + a) :=
  fun x => Fin.append
    (fun r => Fin.append (ConPolyZono.blkDiag a A r) (fun _ => zero))
    (fun _ => Fin.append (fun _ => zero) (fun _ => one)) x

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
