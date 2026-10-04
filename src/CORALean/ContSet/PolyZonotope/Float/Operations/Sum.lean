import CORALean.ContSet.PolyZonotope.Float.Operations.CenterResidual
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Residual
import CORALean.ContSet.Interval.Float.Operations.Origin
import CORALean.ContSet.PolyZonotope.Real.Operations.Sum
import CORALean.ContSet.PolyZonotope.Float.Operations.SumErr

/-!
# `PolyZonotope.sum`, over a floating-point scalar

CORA's `@polyZonotope/sum`: `pZ` summed with the sets `L 0, ..., L (m-1)` over `pZ`'s factors; the
generators and exponent columns are appended, the centres added. The float centre is the lower of
the directed sums and its rounding, with the error boxes of all the summands, goes into the error
box (`sumErr`, `Interval.residual`). The correct sum, not CORA's loop (see the real layer's
`sumCora`).
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `pZ` summed with `L 0, ..., L (m-1)` over `pZ`'s factors. -/
def PolyZonotope.sum {m : ℕ} (pZ : PolyZonotope 𝕋 n) (L : Fin m → PolyZonotope 𝕋 n)
    (hp : ∀ i, (L i).p = pZ.p) : PolyZonotope 𝕋 n where
  p := pZ.p
  h := pZ.h + ∑ i, (L i).h
  q := pZ.q + ∑ i, (L i).q
  c := fun i => addDown (pZ.c i) (sumDown fun l => (L l).c i)
  G := fun i => Fin.append (pZ.G i) fun j =>
    (L (finSigmaFinEquiv.symm j).1).G i (finSigmaFinEquiv.symm j).2
  E := fun k => Fin.append (pZ.E k) fun j =>
    (L (finSigmaFinEquiv.symm j).1).E (Fin.cast (hp _).symm k) (finSigmaFinEquiv.symm j).2
  GI := fun i => Fin.append (pZ.GI i) fun j =>
    (L (finSigmaFinEquiv.symm j).1).GI i (finSigmaFinEquiv.symm j).2
  err := ((pZ.err.plus (PolyZonotope.sumErr m fun i => (L i).err)).plus
    (Interval.residual (fun i => addDown (pZ.c i) (sumDown fun l => (L l).c i))
      (fun i => addUp (pZ.c i) (sumUp fun l => (L l).c i))
      (fun i => addDown (pZ.c i) (sumDown fun l => (L l).c i))))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
