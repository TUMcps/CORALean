module

public import CORALean.ContSet.HPolytope.Float.Operations.ScaleDevLo
public import CORALean.ContSet.HPolytope.Float.Operations.ScaleDevHi
public import CORALean.ContSet.HPolytope.Float.Operations.AnchorEqs
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `HPolytope.scaleRows`: rows scaled by given numbers, the rounding paid on the right-hand side

CORA's `priv_normalizeConstraints` on the stored floats, with the divisors given: `sA i` for
inequality row `i` and `sE i` for equality row `i`. Every entry of a scaled row is rounded down
(`mulDown`), which names a slightly different halfspace, so the difference is absorbed on the
right-hand side over a box `dom` of interest: an inequality's `b` is raised by the least value of
the deviation `(s a - ã)ᵀ x` (`scaleDevLo`). An equality cannot be raised: its scaled row reads, on
a point of the polytope in `dom`, between the two ends the deviation's range allows, so the upper
end is stored and the gap to the lower one is the residual `anchorEqs` moves the point across,
paying the certified step into the error box (or, without a certificate, writing the equality as the
two inequalities it stands for). The scaled polytope contains the original one inside `dom`.

The rows only are read: the error box is not. A polytope with a box is brought to this form by
`absorbRounding` first.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]  {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Row `i` multiplied by `sA i` (`sE i`), the rounding moved to the right-hand sides. -/
def HPolytope.scaleRows (P : HPolytope 𝕋 (Vec 𝕋 n)) (sA : Fin P.m → 𝕋) (sE : Fin P.me → 𝕋)
    (dom : Interval (Vec 𝕋 n)) : HPolytope 𝕋 (Vec 𝕋 n) :=
  -- the scaled rows, an equality at the upper end of where its scaled row reads
  let Q : HPolytope 𝕋 (Vec 𝕋 n) :=
    { m := P.m
      A := fun i j => mulDown (P.A i j) (sA i)
      b := fun i => subUp (mulUp (P.b i) (sA i)) (HPolytope.scaleDevLo (P.A i) (sA i) dom)
      me := P.me
      Ae := fun i j => mulDown (P.Ae i j) (sE i)
      be := fun i => subUp (mulUp (P.be i) (sE i)) (HPolytope.scaleDevLo (P.Ae i) (sE i) dom)
      b_error := fun _ => zero
      be_error := fun _ => zero
      I_error := Interval.origin n }
  -- and how far below it the lower end can lie
  Q.anchorEqs fun i =>
    subUp (Q.be i) (subDown (mulDown (P.be i) (sE i)) (HPolytope.scaleDevHi (P.Ae i) (sE i) dom))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
