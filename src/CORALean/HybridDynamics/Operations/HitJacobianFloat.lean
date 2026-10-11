import CORALean.ContSet.Interval.Float.Operations.MulHi
import CORALean.ContSet.Interval.Float.Operations.MulLo
import CORALean.ContSet.Interval.Float.Operations.Recip

/-!
# A float interval matrix holding the hitting point's Jacobian

`GuardMap.hitJacobian`, [1, Prop. 2]'s
`L_il = I_il + A_il(d − nᵀx₀)/Λ + (Ax₀ + b)ᵢΘ_l/Λ²`, `Λ = nᵀ(Ax₀ + b)`, `Υ = nᵀA`,
`Θ = −nΛ − (d − nᵀx₀)Υᵀ`, enclosed entrywise with directed rounding, one `let` per quantity:
dot products by `dotDown`/`dotUp`, products by their corners, `1/Λ` by `Interval.recip` and
`1/Λ²` as its square. `none` when the interval of `Λ` is not certified to exclude `0`.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 2]: an interval matrix holding `L(x₀)`, `none` if `0` may be in `Λ`'s box. -/
def GuardMap.hitJacobianFloat (A : Mat 𝕋 n n) (b nv : Vec 𝕋 n) (d : 𝕋) (x₀ : Vec 𝕋 n) :
    Option (Interval (Mat 𝕋 n n)) :=
  let y : Interval (Vec 𝕋 n) :=                                       -- `Ax₀ + b`
    ⟨fun i => addDown (dotDown (A i) x₀) (b i), fun i => addUp (dotUp (A i) x₀) (b i)⟩
  let ΛLo := sumDown fun i => Interval.mulLo (nv i) (nv i) (y.inf i) (y.sup i)  -- `Λ = nᵀy`
  let ΛHi := sumUp fun i => Interval.mulHi (nv i) (nv i) (y.inf i) (y.sup i)
  let Λinv := Interval.recip (⟨fun _ => ΛLo, fun _ => ΛHi⟩ : Interval (Vec 𝕋 1))  -- `1/Λ`
  let Λinv2Lo := Interval.mulLo (Λinv.inf 0) (Λinv.sup 0) (Λinv.inf 0) (Λinv.sup 0)  -- `1/Λ²`
  let Λinv2Hi := Interval.mulHi (Λinv.inf 0) (Λinv.sup 0) (Λinv.inf 0) (Λinv.sup 0)
  let numLo := subDown d (dotUp nv x₀)                                 -- `d − nᵀx₀`
  let numHi := subUp d (dotDown nv x₀)
  let τLo := Interval.mulLo numLo numHi (Λinv.inf 0) (Λinv.sup 0)     -- `(d − nᵀx₀)/Λ`
  let τHi := Interval.mulHi numLo numHi (Λinv.inf 0) (Λinv.sup 0)
  let ΥLo : Vec 𝕋 n := fun l => dotDown nv fun j => A j l             -- `Υ = nᵀA`
  let ΥHi : Vec 𝕋 n := fun l => dotUp nv fun j => A j l
  let ΘLo : Vec 𝕋 n := fun l =>                                       -- `Θ = −nΛ − (d − nᵀx₀)Υ`
    subDown (neg (Interval.mulHi ΛLo ΛHi (nv l) (nv l)))
      (Interval.mulHi numLo numHi (ΥLo l) (ΥHi l))
  let ΘHi : Vec 𝕋 n := fun l =>
    subUp (neg (Interval.mulLo ΛLo ΛHi (nv l) (nv l)))
      (Interval.mulLo numLo numHi (ΥLo l) (ΥHi l))
  let yΘLo : Mat 𝕋 n n := fun i l => Interval.mulLo (y.inf i) (y.sup i) (ΘLo l) (ΘHi l)  -- `yᵢΘ_l`
  let yΘHi : Mat 𝕋 n n := fun i l => Interval.mulHi (y.inf i) (y.sup i) (ΘLo l) (ΘHi l)
  if ltStrict zero ΛLo || ltStrict ΛHi zero then                       -- `Λ ≠ 0`, certified
    some ⟨fun i l => addDown (addDown (if i = l then one else zero)  -- `I + Aτ + yΘ/Λ²`
        (Interval.mulLo (A i l) (A i l) τLo τHi))
        (Interval.mulLo (yΘLo i l) (yΘHi i l) Λinv2Lo Λinv2Hi),
      fun i l => addUp (addUp (if i = l then one else zero)
        (Interval.mulHi (A i l) (A i l) τLo τHi))
        (Interval.mulHi (yΘLo i l) (yΘHi i l) Λinv2Lo Λinv2Hi)⟩
  else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
