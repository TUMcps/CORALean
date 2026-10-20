module

public import CORALean.ContSet.ZonoBundle.Float.Operations.BoundDotLP
public import CORALean.ContSet.ZonoBundle.Float.Operations.IntervalAll

@[expose] public section

/-!
# `ZonoBundle.intervalSupportFunc`, over a floating-point scalar

The bundle's box from the support function of the intersection in the directions `±eᵢ`, as over
ℝ, each value bounded by the bundle's linear program (`ZonoBundle.boundDotLP`: the stacked
generators' constrained zonotope, a dual certificate the exact simplex proposes and rounded
arithmetic checks). A certified bound is an upper bound only, so each end is kept where it
improves on CORA's box of the members' boxes (`intervalAll`), `minimum` and `maximum` being
exact: the result is never larger than CORA's box and is its support function up to rounding
where the simplex's weights are optimal. `2n` linear programs, against CORA's `O(n·p)` sum per
member, so this is the tight and slow box beside CORA's cheap one.

## Inputs
* `zB` – float zonotope bundle

## Hypotheses
* `hk` – the bundle has a member

## Output
* the box from the support function in the axis directions
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The bundle's box from its support function in `±eᵢ`, each end kept inside CORA's box. -/
def ZonoBundle.intervalSupportFunc (zB : ZonoBundle (Vec 𝕋 n)) (hk : 0 < zB.k) :
    Interval (Vec 𝕋 n) :=
  -- CORA's box: the intersection of the members' boxes
  let B := zB.intervalAll hk
  -- the bundle's support value in `eᵢ`, by its linear program
  let up : Vec 𝕋 n := fun i => (zB.boundDotLP hk (c := LinearMap.proj i)
    (fun j => if j = i then one else zero) fun x => by
      simp [apply_ite toReal, toReal_one, toReal_zero]).val
  -- and in `-eᵢ`
  let dn : Vec 𝕋 n := fun i => (zB.boundDotLP hk (c := -LinearMap.proj i)
    (fun j => if j = i then neg one else zero) fun x => by
      simp [apply_ite toReal, toReal_neg, toReal_one, toReal_zero]).val
  -- each end where it improves on CORA's
  ⟨fun i => maximum (B.inf i) (neg (dn i)), fun i => minimum (B.sup i) (up i)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
