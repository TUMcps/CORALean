module

public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Operations.Recip

@[expose] public section

/-!
# A float box holding where the constant flow hits the guard

`GuardMap.hitPoint`, `y_h(x₀) = x₀ + (Ax₀ + b)(d − nᵀx₀)/Λ`, `Λ = nᵀ(Ax₀ + b)`, of [1, Sec. 5.4],
enclosed with directed rounding: `Ax₀ + b` and `d − nᵀx₀` by `dotDown`/`dotUp`, `Λ` as a sum of
corner products, `1/Λ` by `Interval.recip`, and the products by their corners. `none` when the
interval of `Λ` is not certified to exclude `0`, where `y_h` is not defined.

## Inputs
* `A` – flow matrix
* `b` – flow offset
* `nv` – guard normal
* `d` – guard offset
* `x₀` – initial state

## Output
* box holding the hit point, none if undefined

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

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A box holding `y_h(x₀) = x₀ + (Ax₀ + b)(d − nᵀx₀)/Λ`, `none` if `0` may be in `Λ`'s box. -/
def GuardMap.hitPointFloat (A : Mat 𝕋 n n) (b nv : Vec 𝕋 n) (d : 𝕋) (x₀ : Vec 𝕋 n) :
    Option (Interval (Vec 𝕋 n)) :=
  let y : Interval (Vec 𝕋 n) :=                                       -- `Ax₀ + b`
    ⟨fun i => addDown (dotDown (A i) x₀) (b i), fun i => addUp (dotUp (A i) x₀) (b i)⟩
  let ΛLo := sumDown fun i => Interval.mulLo (nv i) (nv i) (y.inf i) (y.sup i)  -- `Λ = nᵀy`
  let ΛHi := sumUp fun i => Interval.mulHi (nv i) (nv i) (y.inf i) (y.sup i)
  let Λinv := Interval.recip (⟨fun _ => ΛLo, fun _ => ΛHi⟩ : Interval (Vec 𝕋 1))  -- `1/Λ`
  let numLo := subDown d (dotUp nv x₀)                                 -- `d − nᵀx₀`
  let numHi := subUp d (dotDown nv x₀)
  let τLo := Interval.mulLo numLo numHi (Λinv.inf 0) (Λinv.sup 0)     -- `(d − nᵀx₀)/Λ`
  let τHi := Interval.mulHi numLo numHi (Λinv.inf 0) (Λinv.sup 0)
  if ltStrict zero ΛLo || ltStrict ΛHi zero then                       -- `Λ ≠ 0`, certified
    some ⟨fun i => addDown (x₀ i) (Interval.mulLo τLo τHi (y.inf i) (y.sup i)),
      fun i => addUp (x₀ i) (Interval.mulHi τLo τHi (y.inf i) (y.sup i))⟩
  else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
