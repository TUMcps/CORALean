module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Basic
public import CORALean.ContSet.Ellipsoid.Float.Operations.Inflate
public import CORALean.ContSet.Ellipsoid.Float.Operations.IsPsd
public import CORALean.ContSet.Ellipsoid.Float.Operations.Materialise
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `Ellipsoid.intersectStripGollamudi`, over a floating-point scalar

The real layer's corrected Gollamudi update (CORA's `@ellipsoid/intersectStrip`) for **one**
strip `|c x - y| ≤ φ`. With `G = Q^(1/2)` and `x = q + G u`, the strip is `|vᵀ u - δ| ≤ φ` for
`v = G cᵀ`, `δ = y - c q`; with `ν = vᵀ v = c Q cᵀ` and `s = 1 - λ + λ ν` the result has center
`q + κ W`, `W = G v = Q cᵀ`, `κ = λ δ / s` (the real center), and the shape
`α² Q + (2αβ + β²ν) W Wᵀ` of the factor `G (α I + β v vᵀ)`, with
`(α I + β v vᵀ)² ⪰ σ² ((1 - λ) I + λ v vᵀ)⁻¹`; for `Q` invertible that is the real shape
`σ² invQ⁻¹` (`Theorems/ExistsBallOfStrip`). Only `Q`, `c` and `W` enter, never `G`.

Nothing is trusted: `α`, `g` are `sqrtUp` of `σ²/(1 - λ)` and `σ²/s`, `β ≤ 0` aims at
`α + β ν = g`, and the proof uses only the checks `0 < γ_lo`, `g ≤ γ_lo` on a lower bound of
`α + β ν`. The input's box widens `φ` by `Σᵢ |cᵢ| max(|infᵢ|, |supᵢ|)` and the rounding gap of `δ`,
and is carried over; the center is stored at its lower rounding and the gap paid into the box, the
shape computed as an interval matrix and stored rounded upward (`inflate`). A `Q` that `isPsd`
cannot certify, a failed check, or `λ` not certified in `[0, 1)` returns `E`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   15-October-2026
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
  -- `W = Q cᵀ`, between its two roundings
  let wLoV : Vector 𝕋 n := Vector.ofFn fun i => mulVecDown E.Q c i
  let wHiV : Vector 𝕋 n := Vector.ofFn fun i => mulVecUp E.Q c i
  let wLo : Vec 𝕋 n := fun i => wLoV[i.val]'i.isLt
  let wHi : Vec 𝕋 n := fun i => wHiV[i.val]'i.isLt
  -- the innovation `δ = y - c q`, rounded down, and its rounding gap
  let δ : 𝕋 := subDown y (dotUp c E.q)
  let eδ : 𝕋 := subUp (subUp y (dotDown c E.q)) δ
  -- the strip widened by the box, `|c e| ≤ Σᵢ |cᵢ| max(|infᵢ|, |supᵢ|)`, and by the gap
  let mag : Vec 𝕋 n := fun i => maximum (absolute (E.I_error.inf i)) (absolute (E.I_error.sup i))
  let φ' : 𝕋 := addUp (addUp φ (dotUp (fun i => absolute (c i)) mag)) eδ
  -- `ν = c Q cᵀ`, `1 - λ` and `s = 1 - λ + λ ν`, each from both sides
  let νLo : 𝕋 := maximum zero (E.quadDown c)
  let νHi : 𝕋 := E.quadUp c
  let om : 𝕋 := subDown one lam
  let omHi : 𝕋 := subUp one lam
  let sLo : 𝕋 := maximum om (addDown om (mulDown lam νLo))
  let sHi : 𝕋 := addUp omHi (mulUp lam νHi)
  -- `sigma_sq = 1 - λ + λ φ² - λ (1 - λ) δ² / s`, from above
  let corr : 𝕋 :=
    divDown (mulDown (maximum zero (mulDown lam om)) (maximum zero (mulDown δ δ))) sHi
  let S : 𝕋 := subUp (addUp omHi (mulUp lam (mulUp φ' φ'))) corr
  -- the factor `N = α I + β v vᵀ`: `α ≥ √(σ²/(1-λ))`, `α + β ν ≥ g ≥ √(σ²/s)`
  let α : 𝕋 := sqrtUp steps (divUp S om)
  let g : 𝕋 := sqrtUp steps (divUp S sLo)
  let β : 𝕋 := if ltStrict zero νHi = true then minimum zero (divUp (subUp g α) νHi) else zero
  let γLo : 𝕋 := addDown α (mulDown β νHi)
  -- `κ = λ δ / s`, between two roundings
  let aLo : 𝕋 := mulDown lam δ
  let aHi : 𝕋 := mulUp lam δ
  let κLo : 𝕋 := minimum (divDown aLo sLo) (divDown aLo sHi)
  let κHi : 𝕋 := maximum (divUp aHi sLo) (divUp aHi sHi)
  -- the center `q + κ W`
  let qLo : Vec 𝕋 n := fun i => addDown (E.q i) (Interval.mulLo κLo κHi (wLo i) (wHi i))
  let qHi : Vec 𝕋 n := fun i => addUp (E.q i) (Interval.mulHi κLo κHi (wLo i) (wHi i))
  -- the shape `α² Q + μ W Wᵀ`, `μ = 2αβ + β² ν`, entrywise between two roundings
  let b2νLo : 𝕋 := Interval.mulLo (mulDown β β) (mulUp β β) νLo νHi
  let b2νHi : 𝕋 := Interval.mulHi (mulDown β β) (mulUp β β) νLo νHi
  let μLo : 𝕋 := addDown (addDown (mulDown α β) (mulDown α β)) b2νLo
  let μHi : 𝕋 := addUp (addUp (mulUp α β) (mulUp α β)) b2νHi
  let X : Interval (Mat 𝕋 n n) :=
    ⟨fun i j => addDown (Interval.mulLo (mulDown α α) (mulUp α α) (E.Q i j) (E.Q i j))
        (Interval.mulLo μLo μHi (Interval.mulLo (wLo i) (wHi i) (wLo j) (wHi j))
          (Interval.mulHi (wLo i) (wHi i) (wLo j) (wHi j))),
      fun i j => addUp (Interval.mulHi (mulDown α α) (mulUp α α) (E.Q i j) (E.Q i j))
        (Interval.mulHi μLo μHi (Interval.mulLo (wLo i) (wHi i) (wLo j) (wHi j))
          (Interval.mulHi (wLo i) (wHi i) (wLo j) (wHi j)))⟩
  if le zero lam = true ∧ ltStrict zero om = true ∧ ltStrict zero γLo = true ∧ le g γLo = true
    ∧ Ellipsoid.isPsd E.Q = true
  then
    Ellipsoid.materialise
      { Q := Ellipsoid.inflate X
        q := qLo
        I_error := E.I_error.plus (Interval.residual qLo qHi qLo) }
  else E

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
