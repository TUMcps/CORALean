import CORALean.ContSet.Interval.Float.Operations.MatMul
import CORALean.ContSet.Interval.Float.Operations.MatPlus
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.Interval.Float.Operations.Smul
import CORALean.ContSet.Zonotope.Float.Zonotope
import Mathlib.Data.Fin.VecNotation

/-!
# The matrix zonotope of `y_h`'s second derivatives, over a floating-point scalar

`GuardMap.hitHessianMatZono`, [1, Prop. 3]'s `(C̃⁽ⁱ⁾, G̃^(i,1), …, G̃^(i,1+2p))` from
`R(0) = ⟨c_x, g_x^(1), …, g_x^(p)⟩` and the one-factor enclosure `ψ_c ⊕ [-1, 1]ψ_g` of `Θ/Λ`,
taken here as `ψ_c = −n − τ_c Υᵀ`, `ψ_g = −τ_g Υᵀ` from the centre `τ_c` and radius `τ_g` of an
interval of `τ = (d − nᵀx)/Λ(x)`, the reading of [1, Prop. 3] under which it holds
(`Location.guardIntersectHyperplaneMap`). Every printed formula is one `let`, an interval matrix
built from point matrices by the float `matMul`, `matPlus` and `smul`: vectors are columns
`n × 1` or rows `1 × n` as the formula indexes them, so `A_il Θ_m` is `A_{i·} Θ_c` and
`A_im Θ_l` is `Θ_cᵀ A_{i·}ᵀ`.

The centre is `C̃⁽ⁱ⁾`'s lower end and `G̃^(i,1)` its first generator, and the error box holds
what the rest of their intervals adds at a factor in `[-1, 1]`: `[0, C̄ − C̲] + [-1, 1](Ḡ − G̲)`.
That is the enclosure `GuardMap.hitHessianMatZonoFloat_mem` states, at the factors `(κ, 0, 0)`
of the centre `c_x`, the only point the guard mapping evaluates `Q⁽ⁱ⁾` at. The generators
`G̃^(i,1+α)` and `G̃^(i,1+p+α)` are kept, as CORA keeps them, at the lower ends of their
intervals; nothing is claimed of them.

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
    ⟨fun l m => neg (w₁ l m), fun l m => addUp (wC l m) (w₁ l m)⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
