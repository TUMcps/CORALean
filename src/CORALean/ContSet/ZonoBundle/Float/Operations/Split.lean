module

public import CORALean.ContSet.ZonoBundle.Float.Operations.Intersection
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Float.Operations.Split
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `ZonoBundle.split` over a floating-point scalar

[1, Eq. 2] on the stored floats: the parallelotope `Ψ = Λ box`, the box `B` as a zonotope mapped
by the float directions `Λ` (`Zonotope.mtimes`, its rounding in the error box), split along its
`j`-th generator by the float `Zonotope.split`, each half appended to the bundle. As over ℝ the
box `B` is an argument: CORA's `box(Λ⁻¹ Z_∩)` needs the inverse, which is not computed here.

## Inputs
* `Λ` – edge directions
* `B` – box in the transformed coordinates
* `j` – dimension to cut along
* `zB` – float zonotope bundle

## Output
* the two halves of the bundle

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two halves `Z_∩¹`, `Z_∩²` of [1, Eq. 2], split along the `j`-th column of `Λ`. -/
def ZonoBundle.split (Λ : Mat 𝕋 n n) (B : Interval (Vec 𝕋 n)) (j : Fin n)
    (zB : ZonoBundle (Vec 𝕋 n)) : ZonoBundle (Vec 𝕋 n) × ZonoBundle (Vec 𝕋 n) :=
  let Ψ := Zonotope.mtimes Λ B.zonotope                  -- Ψ = Λ box
  let Ψs := Ψ.split j                                     -- the two halves along `w⁽ʲ⁾`
  (zB.intersection ⟨1, fun _ => Ψs.fst⟩, zB.intersection ⟨1, fun _ => Ψs.snd⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
