module

public import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
public import CORALean.ContSet.Zonotope.Float.Operations.AbsBoundError
public import CORALean.ContSet.Zonotope.Float.Operations.QuadMap
public import CORALean.ContSet.Zonotope.Float.Operations.SumTerms
public import CORALean.ContSet.Zonotope.Float.Operations.UnitIntervalMul

@[expose] public section

/-!
# `Zonotope.quadMapMatZono`, over a floating-point scalar

`Real.Zonotope.quadMapMatZono`, [1, Thm. 1]: the quadratic map `{λ | λᵢ = xᵀQ⁽ⁱ⁾x, x ∈ Z}` with
each `Q⁽ⁱ⁾` ranging over a matrix zonotope `(D⁽ⁱ⁾, K⁽ⁱ'¹⁾, ..., K⁽ⁱ'ᵛ⁾)`, enclosed by
`Z_D ⊕ ([-1, 1] ⊗ Z_K(1)) ⊕ ... ⊕ ([-1, 1] ⊗ Z_K(ν))`. The centres `D⁽ⁱ⁾` are interval
matrices here: a caller computing them with directed rounding knows them only to within a box.
The map is taken at the lower ends `D̲⁽ⁱ⁾`, and what the rest of the box adds,
`xᵀ(D⁽ⁱ⁾ − D̲⁽ⁱ⁾)x`, is bounded by `∑ₗₖ rₗ wₗₖ rₖ`, `r` the float bound of `|x|` over `Z`
(`absBoundError`) and `w = D̄⁽ⁱ⁾ − D̲⁽ⁱ⁾` rounded up, a box the sum takes as a zonotope. Each
`Z_K(j)` and `Z_D` is the float `quadMap`; the `ν` products and the box are added by `plus`.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m ν : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Thm. 1] at interval-matrix centres: `Z_D̲ ⊕ ([-1, 1] ⊗ Z_K(1)) ⊕ ... ⊕ [-e, e]`. -/
def Zonotope.quadMapMatZono (D : Fin m → Interval (Mat 𝕋 n n))
    (K : Fin ν → Fin m → Mat 𝕋 n n) (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 m) :=
  let ZD := Z.quadMap fun i => (D i).inf                 -- `Z_D` at the lower ends
  let ZK : ℕ → Zonotope (Vec 𝕋 m) := fun j =>                  -- `[-1, 1] ⊗ Z_K(j)`
    if hj : j < ν then (Z.quadMap (K ⟨j, hj⟩)).unitIntervalMul else Zonotope.point fun _ => zero
  let r : Vec 𝕋 n := Z.absBoundError                     -- `|xₗ| ≤ rₗ` over `Z`
  let w : Fin m → Mat 𝕋 n n := fun i l k =>              -- the width `D̄ − D̲`, up
    subUp ((D i).sup l k) ((D i).inf l k)
  let e : Vec 𝕋 m := fun i =>                            -- `∑ₗₖ rₗ wₗₖ rₖ`, up
    sumUp fun l => sumUp fun k => mulUp (mulUp (r l) (w i l k)) (r k)
  let ZE := (⟨fun i => neg (e i), e⟩ : Interval (Vec 𝕋 m)).zonotope
  (ZD.plus (Zonotope.sumTerms ZK ν)).plus ZE

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
