module

public import CORALean.ContSet.ZonoBundle.Float.Operations.IntervalAll
public import CORALean.ContSet.ZonoBundle.Float.Operations.Mtimes
public import CORALean.ContSet.ZonoBundle.Float.Operations.Parallelotope
public import CORALean.ContSet.Zonotope.Float.Operations.BasisInverse
public import CORALean.ContSet.Interval.Float.Operations.Magnitude

@[expose] public section

/-!
# `ZonoBundle.enclosingParallelotope`, over a floating-point scalar

`Γ box(Γ⁻¹ Z_∩)` [1, Eq. 2], the parallelotope with edges along the columns of `Γ` around a
bundle, which CORA's `shrink` and `reduceCombined` build. `Γ⁻¹` is a candidate `H` from
`Zonotope.basisInverse`, the box that of the bundle mapped by `H` (`intervalAll`), and
`parallelotope` pays the residual `(1 - Γ H) x` for `|x|` up to the bundle's own box. Where the
row-sum bound of `1 - Γ H` is above one half (`Γ` singular, or badly inverted), `Γ` is replaced by
the identity, as the exact layer replaces a singular `Γ`; the result holds the bundle at any `Γ`.

## Inputs
* `zB` – float zonotope bundle
* `Γ` – edge directions

## Hypotheses
* `hk` – the bundle has a member

## Output
* parallelotope along the given directions enclosing the bundle

## References

* [1] [M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of Reachable
      Sets". 2011 50th IEEE Conference on Decision and Control and European Control Conference
      (CDC-ECC 2011), 2011.](../../../../../../references/2011/althoff-cdc-zonotope-bundles.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Γ box(Γ⁻¹ Z_∩)` of a bundle with a member, at `Γ` if its candidate inverse checks, at the
identity if not. -/
def ZonoBundle.enclosingParallelotope (zB : ZonoBundle (Vec 𝕋 n)) (hk : 0 < zB.k)
    (Γ : Mat 𝕋 n n) : Zonotope (Vec 𝕋 n) :=
  let Hc := Zonotope.basisInverse Γ                                  -- inv(Γ), a candidate
  let ok := le (Zonotope.rightInvQ Γ Hc) (half one)                  -- checks: ‖1 - Γ H‖ ≤ 1/2
  let I : Mat 𝕋 n n := fun i j => if i = j then one else zero
  let Γ' := if ok then Γ else I                                      -- directions to undo
  let H := if ok then Hc else I
  let B := (zB.mtimes H).intervalAll hk                              -- box(Γ⁻¹ Z_∩)
  let m := maximumOver (zB.intervalAll hk).magnitude                 -- reach of the bundle
  ZonoBundle.parallelotope Γ' H B m                                  -- Γ' box(Γ'⁻¹ Z_∩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
