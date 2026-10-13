module

public import CORALean.ContSet.HPolytope.Float.Operations.IsZeroVec
public import CORALean.ContSet.HPolytope.Float.Operations.Restrict
public import CORALean.ContSet.HPolytope.Float.Operations.EmptySet

@[expose] public section

/-!
# `HPolytope.dropZeros`: the zero-row step of `compact_`

CORA's `priv_compact_zeros` on the rows as stored: a zero inequality row `0 ≤ b` with `b`
certified negative (`ltStrict`), or a zero equality row whose interval is certified to miss `0`,
is infeasible and the result is the empty set. Otherwise the zero rows certified to hold
(`0 ≤ b` with `0 ≤ b` certified by `le`, `0` certified inside the interval) are deleted by
`restrict`; a row whose certificate fails is kept. Nothing rounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The empty set if a zero row is certified infeasible, else the rows not certified trivial. -/
def HPolytope.dropZeros (Q : HPolytope 𝕋 (Vec 𝕋 n)) : HPolytope 𝕋 (Vec 𝕋 n) :=
  if (List.finRange Q.m).any (fun i => HPolytope.isZeroVec (Q.A i) && ltStrict (Q.b i) zero)
      || (List.finRange Q.me).any (fun r => HPolytope.isZeroVec (Q.Ae r) &&
        (ltStrict zero (Q.be.inf r) || ltStrict (Q.be.sup r) zero)) then
    HPolytope.emptySet 𝕋 n
  else
    Q.restrict (fun i => !(HPolytope.isZeroVec (Q.A i) && le zero (Q.b i)))
      (fun r => !(HPolytope.isZeroVec (Q.Ae r) && le (Q.be.inf r) zero && le zero (Q.be.sup r)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
