module

public import CORALean.ContSet.Ellipsoid.Float.Operations.GeneratorError
public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Operations.Plus
public import CORALean.ContSet.Interval.Float.Operations.Residual
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `Ellipsoid.intersectStripGollamudi`, over a floating-point scalar

The real layer's corrected Gollamudi update (CORA's `@ellipsoid/intersectStrip`) for **one**
strip `|c x - y| ≤ φ`, worked in the coefficient space of the stored generators, so neither `Q⁻¹`
nor a matrix square root is formed. For `x = q + G u` the strip is `|vᵀ u - δ| ≤ φ` with
`v = Gᵀ cᵀ`, `δ = y - c q`; with `ν = vᵀ v`, `s = 1 - λ + λ ν` the result has centre
`q + κ G v`, `κ = λ δ / s` (the real centre), and generators `α G + β (G v) vᵀ`, the image of
`N = α I + β v vᵀ` with `N² ⪰ σ² ((1 - λ) I + λ v vᵀ)⁻¹`; for `Q = G Gᵀ`, `G` invertible, that is
the real shape `σ² invQ⁻¹` (`Theorems/ExistsBallOfStrip`).

Nothing is trusted: `α`, `g` are `sqrtUp` of `σ²/(1 - λ)` and `σ²/s`, `β ≤ 0` aims at
`α + β ν = g`, and the proof uses only the checks `0 < γ_lo`, `g ≤ γ_lo` on a lower bound of
`α + β ν`. The input's box widens `φ` by `Σᵢ |cᵢ| max(|infᵢ|, |supᵢ|)`, with the rounding gaps of
`v` and `δ`, and is carried over; centre and generators are stored at their lower roundings and
the gaps paid into the box. A failed check, or `λ` not certified in `[0, 1)`, returns `E`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Gollamudi update of `E` by the strip `|c x - y| ≤ φ` at the weight `lam`; `steps` Newton
steps for the two square roots. -/
def Ellipsoid.intersectStripGollamudi (steps : ℕ) (E : Ellipsoid 𝕋 n) (c : Vec 𝕋 n)
    (φ y lam : 𝕋) : Ellipsoid 𝕋 n :=
  -- `v = (c G)ᵀ`, rounded down, and its rounding gap
  let vV : Vector 𝕋 E.k := Vector.ofFn fun j => dotDown (fun i => E.G i j) c
  let v : Vec 𝕋 E.k := fun j => vV[j.val]'j.isLt
  let ev : Vec 𝕋 E.k := fun j => subUp (dotUp (fun i => E.G i j) c) (v j)
  -- the innovation `δ = y - c q`, rounded down, and its rounding gap
  let δ : 𝕋 := subDown y (dotUp c E.q)
  let eδ : 𝕋 := subUp (subUp y (dotDown c E.q)) δ
  -- the strip widened by the box, `|c e| ≤ Σᵢ |cᵢ| max(|infᵢ|, |supᵢ|)`, and by both gaps
  let mag : Vec 𝕋 n := fun i => maximum (absolute (E.err.inf i)) (absolute (E.err.sup i))
  let φ' : 𝕋 := addUp (addUp (addUp φ (dotUp (fun i => absolute (c i)) mag)) (sumUp ev)) eδ
  -- `ν = vᵀ v`, `1 - λ` and `s = 1 - λ + λ ν`, each from both sides
  let νLo : 𝕋 := maximum zero (dotDown v v)
  let νHi : 𝕋 := sqSumUp fun j => absolute (v j)
  let om : 𝕋 := subDown one lam
  let omHi : 𝕋 := subUp one lam
  let sLo : 𝕋 := maximum om (addDown om (mulDown lam νLo))
  let sHi : 𝕋 := addUp omHi (mulUp lam νHi)
  -- `sigma_sq = 1 - λ + λ φ² - λ (1 - λ) δ² / s`, from above
  let corr : 𝕋 :=
    divDown (mulDown (maximum zero (mulDown lam om)) (maximum zero (mulDown δ δ))) sHi
  let S : 𝕋 := subUp (addUp omHi (mulUp lam (mulUp φ' φ'))) corr
  -- the generator factor `N = α I + β v vᵀ`: `α ≥ √(σ²/(1-λ))`, `α + β ν ≥ g ≥ √(σ²/s)`
  let α : 𝕋 := sqrtUp steps (divUp S om)
  let g : 𝕋 := sqrtUp steps (divUp S sLo)
  let β : 𝕋 := if ltStrict zero νHi = true then minimum zero (divUp (subUp g α) νHi) else zero
  let γLo : 𝕋 := addDown α (mulDown β νHi)
  -- `κ = λ δ / s` and `G v`, each between two roundings
  let aLo : 𝕋 := mulDown lam δ
  let aHi : 𝕋 := mulUp lam δ
  let κLo : 𝕋 := minimum (divDown aLo sLo) (divDown aLo sHi)
  let κHi : 𝕋 := maximum (divUp aHi sLo) (divUp aHi sHi)
  let wLoV : Vector 𝕋 n := Vector.ofFn fun i => dotDown (E.G i) v
  let wHiV : Vector 𝕋 n := Vector.ofFn fun i => dotUp (E.G i) v
  let wLo : Vec 𝕋 n := fun i => wLoV[i.val]'i.isLt
  let wHi : Vec 𝕋 n := fun i => wHiV[i.val]'i.isLt
  -- the centre `q + κ G v`
  let qLo : Vec 𝕋 n := fun i => addDown (E.q i) (Interval.mulLo κLo κHi (wLo i) (wHi i))
  let qHi : Vec 𝕋 n := fun i => addUp (E.q i) (Interval.mulHi κLo κHi (wLo i) (wHi i))
  -- the generators `α G + β (G v) vᵀ`
  let bLo : Vec 𝕋 n := fun i => Interval.mulLo β β (wLo i) (wHi i)
  let bHi : Vec 𝕋 n := fun i => Interval.mulHi β β (wLo i) (wHi i)
  let GLo : Mat 𝕋 n E.k := fun i j =>
    addDown (mulDown α (E.G i j)) (Interval.mulLo (bLo i) (bHi i) (v j) (v j))
  let GHi : Mat 𝕋 n E.k := fun i j =>
    addUp (mulUp α (E.G i j)) (Interval.mulHi (bLo i) (bHi i) (v j) (v j))
  let GD : Mat 𝕋 n E.k := fun i j => subUp (GHi i j) (GLo i j)
  if le zero lam = true ∧ ltStrict zero om = true ∧ ltStrict zero γLo = true ∧ le g γLo = true
  then
    Ellipsoid.materialise
      { k := E.k
        q := qLo
        G := GLo
        err := (E.err.plus (Interval.residual qLo qHi qLo)).plus (Ellipsoid.generatorError GD) }
  else E

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
