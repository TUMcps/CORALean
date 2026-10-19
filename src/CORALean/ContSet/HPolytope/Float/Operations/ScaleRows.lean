module

public import CORALean.ContSet.HPolytope.Float.Operations.ScaleDevLo
public import CORALean.ContSet.HPolytope.Float.Operations.ScaleDevHi
public import CORALean.ContSet.HPolytope.Float.Operations.SetRhs
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `HPolytope.scaleRows`: rows scaled by given numbers, the rounding paid on the right-hand side

CORA's `priv_normalizeConstraints` on the stored floats, with the divisors given: `sA i` for
inequality row `i` and `sE i` for equality row `i`. Every entry of a scaled row is rounded down
(`mulDown`), which names a slightly different halfspace, so the difference is absorbed on the
right-hand side over a box `dom` of interest. On a point of the polytope in `dom`, a scaled row's
exact bound is the scaled bound less the deviation `(s a - ã)ᵀ x`, which lies between `scaleDevLo`
and `scaleDevHi`; `setRhs` stores the lower end of that enclosure and pays its width into the row's
slack (#218). So an inequality's `b` is not raised and an equality stays an equality, a slab as
wide as the enclosure. The scaled polytope contains the original one inside `dom`.

The rows only are read: the error box and the slacks are not. A polytope with either is brought to
this form by `absorbRounding` first.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]  {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Row `i` multiplied by `sA i` (`sE i`), the rounding in the rows' slacks. -/
def HPolytope.scaleRows (P : HPolytope 𝕋 (Vec 𝕋 n)) (sA : Fin P.m → 𝕋) (sE : Fin P.me → 𝕋)
    (dom : Interval (Vec 𝕋 n)) : HPolytope 𝕋 (Vec 𝕋 n) :=
  -- the scaled rows, read as error-free
  let Q : HPolytope 𝕋 (Vec 𝕋 n) :=
    { m := P.m
      A := fun i j => mulDown (P.A i j) (sA i)
      b := P.b
      me := P.me
      Ae := fun i j => mulDown (P.Ae i j) (sE i)
      be := P.be
      b_error := fun _ => zero
      be_error := fun _ => zero
      I_error := Interval.origin n }
  -- each right-hand side: the scaled bound less the deviation, between its two ends
  Q.setRhs
    (fun i => subDown (mulDown (P.b i) (sA i)) (HPolytope.scaleDevHi (P.A i) (sA i) dom))
    (fun i => subUp (mulUp (P.b i) (sA i)) (HPolytope.scaleDevLo (P.A i) (sA i) dom))
    (fun i => subDown (mulDown (P.be i) (sE i)) (HPolytope.scaleDevHi (P.Ae i) (sE i) dom))
    (fun i => subUp (mulUp (P.be i) (sE i)) (HPolytope.scaleDevLo (P.Ae i) (sE i) dom))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
