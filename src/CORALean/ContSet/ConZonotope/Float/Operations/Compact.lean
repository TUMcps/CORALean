module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope

@[expose] public section

/-!
# `ConZonotope.compact` over a floating-point scalar

CORA's `@conZonotope/compact_` with method `'zeros'` (also what `'all'` does) on the stored
floats: delete the equality rows that are `0 x ∈ be` with `0` in the interval, then the
generators whose column of `[G; A; Ae]` is zero. A row or column goes only when every entry is
certified zero by `le` both ways, so a `le` that fails keeps it: nothing rounds, and the set is
the same (`compact_exact`). Inequality rows stay, as over ℝ; the kept generators and rows keep
their order. Tolerance `0`; CORA's `eps` removes columns below it as well.
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

def ConZonotope.compact (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  -- an entry certified zero
  let isZero : 𝕋 → Bool := fun a => le a zero && le zero a
  -- the generators kept: some entry of the column of `[G; A; Ae]` not certified zero
  let S := Finset.univ.filter fun j : Fin cZ.h =>
    !((List.finRange n).all (fun i => isZero (cZ.G j i))
      && (List.finRange cZ.P.m).all (fun k => isZero (cZ.P.A k j))
      && (List.finRange cZ.P.me).all (fun k => isZero (cZ.P.Ae k j)))
  -- the equality rows kept: all but the certified `0 x ∈ be` with `0 ∈ be`
  let R := Finset.univ.filter fun r : Fin cZ.P.me =>
    !((List.finRange cZ.h).all (fun j => isZero (cZ.P.Ae r j))
      && le (cZ.P.be.inf r) zero && le zero (cZ.P.be.sup r))
  { h := S.card
    c := cZ.c
    G := fun l => cZ.G (S.orderEmbOfFin rfl l)
    P :=
      { m := cZ.P.m
        A := fun k l => cZ.P.A k (S.orderEmbOfFin rfl l)
        b := cZ.P.b
        me := R.card
        Ae := fun r l => cZ.P.Ae (R.orderEmbOfFin rfl r) (S.orderEmbOfFin rfl l)
        be := ⟨fun r => cZ.P.be.inf (R.orderEmbOfFin rfl r),
               fun r => cZ.P.be.sup (R.orderEmbOfFin rfl r)⟩ }
    E := cZ.E }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
