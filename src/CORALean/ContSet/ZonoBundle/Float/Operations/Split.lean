import CORALean.ContSet.ZonoBundle.Float.Operations.Intersection
import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
import CORALean.ContSet.Zonotope.Float.Operations.Split
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope

/-!
# `ZonoBundle.split` over a floating-point scalar

[1, Eq. 2] on the stored floats: the parallelotope `Ψ = Λ box`, the box `B` as a zonotope mapped
by the float directions `Λ` (`Zonotope.mtimes`, its rounding in the error box), split along its
`j`-th generator by the float `Zonotope.split`, each half appended to the bundle. As over ℝ the
box `B` is an argument: CORA's `box(Λ⁻¹ Z_∩)` needs the inverse, which is not computed here.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two halves `Z_∩¹`, `Z_∩²` of [1, Eq. 2], split along the `j`-th column of `Λ`. -/
def ZonoBundle.split (Λ : Mat 𝕋 n n) (B : Interval (Vec 𝕋 n)) (j : Fin n)
    (zB : ZonoBundle (Vec 𝕋 n)) : ZonoBundle (Vec 𝕋 n) × ZonoBundle (Vec 𝕋 n) :=
  let Ψ := Zonotope.mtimes Λ B.zonotope                  -- Ψ = Λ box
  let Ψs := Ψ.split j                                     -- the two halves along `w⁽ʲ⁾`
  (zB.intersection ⟨1, fun _ => Ψs.1⟩, zB.intersection ⟨1, fun _ => Ψs.2⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
