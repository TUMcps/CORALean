module

public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Operations.Smul
public import CORALean.ContSet.Zonotope.Float.Zonotope
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# The matrix zonotope of `y_h`'s second derivatives, over a floating-point scalar

`GuardMap.hitHessianMatZono`, [1, Prop. 3]'s `(C̃⁽ⁱ⁾, G̃^(i,1), …, G̃^(i,1+2p))` from `R(0)` and
the one-factor enclosure `ψ_c ⊕ [-1, 1]ψ_g` of `Θ/Λ`, taken as `ψ_c = −n − τ_c Υᵀ`,
`ψ_g = −τ_g Υᵀ` from the center `τ_c` and radius `τ_g` of an interval of `τ = (d − nᵀx)/Λ(x)`
(`Location.guardIntersectHyperplaneMap`). Every printed formula is one `let`, an interval matrix
from the float `matMul`, `matPlus` and `smul`. The center is `C̃⁽ⁱ⁾`'s lower end and the error box
holds the rest of the intervals; the enclosure is `GuardMap.hitHessianMatZonoFloat_mem`, at the
factors `(κ, 0, 0)` of `c_x`. The generators `G̃^(i,1+α)`, `G̃^(i,1+p+α)` are kept at the lower
ends of their intervals; nothing is claimed of them.

## Inputs
* `A` – flow matrix
* `b` – flow offset
* `nv` – guard normal
* `d` – guard offset
* `R₀` – initial zonotope
* `τc` – center of the hitting time interval
* `τg` – radius of the hitting time interval
* `i` – output coordinate

## Output
* float matrix zonotope enclosing the numerators

## References

* [1] [M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control,
      2012.](../../../../references/2012/althoff-hscc-avoiding-intersection.md)
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

/-- [1, Prop. 3] at floats: `(C̃⁽ⁱ⁾, G̃^(i,1), …)` from `R(0)`, `τ_c` and `τ_g`. -/
def GuardMap.hitHessianMatZonoFloat (A : Mat 𝕋 n n) (b nv : Vec 𝕋 n) (d : 𝕋)
    (R₀ : Zonotope (Vec 𝕋 n)) (τc τg : 𝕋) (i : Fin n) : Zonotope (Mat 𝕋 n n) :=
  let col : Vec 𝕋 n → Interval (Mat 𝕋 n 1) := fun v => Interval.point fun l _ => v l
  let row : Vec 𝕋 n → Interval (Mat 𝕋 1 n) := fun v => Interval.point fun _ m => v m
  let neg1 : 𝕋 := neg one                                       -- `−1`, exact
  let twoLo : 𝕋 := neg (addUp one one)                          -- `−2`, bracketed
  let twoHi : 𝕋 := neg (addDown one one)
  let cx := R₀.c                                                -- `c_x`
  let gx := R₀.G                                                -- `g_x^(α)`
  let Υ := Interval.matMul (row nv) (Interval.point A)          -- `Υ = nᵀA`, a row
  let ΥT := Interval.matMul (Interval.point fun l j => A j l) (col nv)  -- and a column
  let y := Interval.matPlus (Interval.matMul (Interval.point A) (col cx)) (col b)  -- `A c_x + b`
  let Λ := Interval.matMul (row nv) y                           -- `Λ = nᵀ(A c_x + b)`
  let num := Interval.matPlus (Interval.point fun _ _ => d)     -- `d − nᵀc_x`
    (Interval.smul neg1 neg1 (Interval.matMul (row nv) (col cx)))
  let Θc := Interval.matPlus (Interval.smul neg1 neg1 (Interval.matMul Λ (row nv)))  -- `Θ_c`, (18)
    (Interval.smul neg1 neg1 (Interval.matMul num Υ))
  let ΘcT := Interval.matPlus (Interval.smul neg1 neg1 (Interval.matMul (col nv) Λ))
    (Interval.smul neg1 neg1 (Interval.matMul ΥT num))
  let ψc := Interval.matPlus (Interval.smul neg1 neg1 (col nv))  -- `ψ_c = −n − τ_c Υᵀ`
    (Interval.smul (neg τc) (neg τc) ΥT)
  let ψg := Interval.smul (neg τg) (neg τg) ΥT                  -- `ψ_g = −τ_g Υᵀ`
  let Ω := Interval.matPlus                                     -- `Ω = −nΥ + Υᵀnᵀ`
    (Interval.smul neg1 neg1 (Interval.matMul (col nv) Υ)) (Interval.matMul ΥT (row nv))
  let S := Interval.matPlus Ω (Interval.smul twoLo twoHi (Interval.matMul ψc Υ))  -- `Ω − 2ψ_cΥ`
  let C := Interval.matPlus                                     -- `C̃⁽ⁱ⁾`
    (Interval.matPlus (Interval.matMul (col (A i)) Θc) (Interval.matMul ΘcT (row (A i))))
    (Interval.smul (y.inf i 0) (y.sup i 0) S)
  let G₁ := Interval.smul (y.inf i 0) (y.sup i 0)                -- `G̃^(i,1)`
    (Interval.smul twoLo twoHi (Interval.matMul ψg Υ))
  let Ag : Fin R₀.h → Interval (Mat 𝕋 n 1) := fun α =>          -- `A g_x^(α)`
    Interval.matMul (Interval.point A) (col (gx α))
  let Θg : Fin R₀.h → Interval (Mat 𝕋 1 n) := fun α =>          -- `Θ_g^(α)`, (18)
    Interval.matPlus (Interval.smul neg1 neg1 (Interval.matMul (Interval.matMul (row nv) (Ag α))
      (row nv))) (Interval.matMul (Interval.matMul (row nv) (col (gx α))) Υ)
  let ΘgT : Fin R₀.h → Interval (Mat 𝕋 n 1) := fun α =>
    Interval.matPlus (Interval.smul neg1 neg1 (Interval.matMul (col nv)
      (Interval.matMul (row nv) (Ag α))))
      (Interval.matMul ΥT (Interval.matMul (row nv) (col (gx α))))
  let Gβ : Fin R₀.h → Mat 𝕋 n n := fun α => (Interval.matPlus   -- `G̃^(i,1+α)`, lower ends
    (Interval.matPlus (Interval.matMul (col (A i)) (Θg α)) (Interval.matMul (ΘgT α) (row (A i))))
    (Interval.smul ((Ag α).inf i 0) ((Ag α).sup i 0) S)).inf
  let Gκβ : Fin R₀.h → Mat 𝕋 n n := fun α =>                    -- `G̃^(i,1+p+α)`, lower ends
    (Interval.smul ((Ag α).inf i 0) ((Ag α).sup i 0)
      (Interval.smul twoLo twoHi (Interval.matMul ψg Υ))).inf
  let wC : Mat 𝕋 n n := fun l m => subUp (C.sup l m) (C.inf l m)    -- what `C̃` adds
  let w₁ : Mat 𝕋 n n := fun l m => subUp (G₁.sup l m) (G₁.inf l m)  -- and `G̃^(i,1)`
  ⟨1 + R₀.h + R₀.h, C.inf, Fin.append (Fin.append ![G₁.inf] Gβ) Gκβ,
    ⟨-w₁, fun l m => addUp (wC l m) (w₁ l m)⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
