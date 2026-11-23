module

public import CORALean.Global.Float.Sqrt
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The line of a product on a zonotope

CORA.cpp's `priv_product_line` for `a b`, `a = c_a + x`, `b = c_b + y`, `x = G_a β + r_a`,
`y = G_b β + r_b` (`|r_a| ≤ ρ_a`, `|r_b| ≤ ρ_b`). The line `c_b a + c_a b` leaves `x y - c_a c_b`.
For `k > 0`, `4 x y = (k x + y / k)² - (k x - y / k)²`, the squares at most `S(k)²` and `D(k)²`,
`S(k) = ∑ⱼ |k G_aⱼ + G_bⱼ / k| + k ρ_a + ρ_b / k` (`D` with the difference): `x y` lies in
`[-D(k)² / 4, S(k)² / 4]`, taken at `k = 1` and `k = λ = √(B / A)` (the rests' 1-norms, `λ ≥ τ`).
The offset is the middle minus `c_a c_b`, the error half the width plus CORA.cpp's margin
`w₁ max(hi, -lo) + w₂ |c_a c_b|` and the offset's rounding (zero at nearest: CORA.cpp's order).

## Inputs
* `p` – the square root's Newton steps
* `τ` – the least scale (CORA.cpp's `kTiny`)
* `w₁` – the margin's factor of the larger end (CORA.cpp's `(2 (q + 2) + 16) eps`)
* `w₂` – the margin's factor of the centers' product (CORA.cpp's `16 eps`)
* `ca` – center of `a`
* `cb` – center of `b`
* `Ga` – generators of `a`
* `Gb` – generators of `b`
* `ra` – radius of `a`'s interval center
* `rb` – radius of `b`'s interval center

## Output
* the offset and the error of the line `cb a + ca b`
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The scale `λ = √(B / A)` of the rests' 1-norms `A`, `B` (`1` unless both are positive), kept
above `τ`. -/
@[step_of productLine]
def step_productScale (p : ℕ) (τ : 𝕋) (Ga Gb : Fin q → 𝕋) (ra rb : 𝕋) : 𝕋 :=
  let A := addUp (sumUp fun j => absolute (Ga j)) ra
  let B := addUp (sumUp fun j => absolute (Gb j)) rb
  let both := ltStrict zero A && ltStrict zero B
  maximum (if both then sqrtUp p (divUp B A) else one) τ

/-- `S(k) = ∑ⱼ |k G_aⱼ + G_bⱼ / k| + (k ρ_a + ρ_b / k)`, each term at the larger of its two
roundings, rounded up. -/
@[step_of productLine]
def step_productSumSpan (k : 𝕋) (Ga Gb : Fin q → 𝕋) (ra rb : 𝕋) : 𝕋 :=
  let term := fun j => maximum (absolute (addUp (mulUp (Ga j) k) (divUp (Gb j) k)))
    (absolute (addDown (mulDown (Ga j) k) (divDown (Gb j) k)))
  addUp (sumUp term) (addUp (mulUp ra k) (mulUp rb (divUp one k)))

/-- `D(k) = ∑ⱼ |k G_aⱼ - G_bⱼ / k| + (k ρ_a + ρ_b / k)`, rounded up. -/
@[step_of productLine]
def step_productDiffSpan (k : 𝕋) (Ga Gb : Fin q → 𝕋) (ra rb : 𝕋) : 𝕋 :=
  let term := fun j => maximum (absolute (subUp (mulUp (Ga j) k) (divDown (Gb j) k)))
    (absolute (subDown (mulDown (Ga j) k) (divUp (Gb j) k)))
  addUp (sumUp term) (addUp (mulUp ra k) (mulUp rb (divUp one k)))

/-- The lower end `max(-D(1)² / 4, -D(λ)² / 4)` of `x y`. -/
@[step_of productLine]
def step_productLo (p : ℕ) (τ : 𝕋) (Ga Gb : Fin q → 𝕋) (ra rb : 𝕋) : 𝕋 :=
  let lam := step_productScale p τ Ga Gb ra rb
  let d1 := step_productDiffSpan one Ga Gb ra rb
  let d2 := step_productDiffSpan lam Ga Gb ra rb
  maximum (neg (half (half (mulUp d1 d1)))) (neg (half (half (mulUp d2 d2))))

/-- The upper end `min(S(1)² / 4, S(λ)² / 4)` of `x y`. -/
@[step_of productLine]
def step_productHi (p : ℕ) (τ : 𝕋) (Ga Gb : Fin q → 𝕋) (ra rb : 𝕋) : 𝕋 :=
  let lam := step_productScale p τ Ga Gb ra rb
  let s1 := step_productSumSpan one Ga Gb ra rb
  let s2 := step_productSumSpan lam Ga Gb ra rb
  minimum (half (half (mulUp s1 s1))) (half (half (mulUp s2 s2)))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The offset `(lo + hi) / 2 - c_a c_b` and the error `(hi - lo) / 2`, plus the offset's
rounding and the margin, of the line `c_b a + c_a b` of `a b`. -/
def productLine (p : ℕ) (τ w₁ w₂ ca cb : 𝕋) (Ga Gb : Fin q → 𝕋) (ra rb : 𝕋) : 𝕋 × 𝕋 :=
  let lo := step_productLo p τ Ga Gb ra rb
  let hi := step_productHi p τ Ga Gb ra rb
  let offset := subDown (half (addDown lo hi)) (mulUp ca cb)
  let offsetUp := subUp (half (addUp lo hi)) (mulDown ca cb)
  let big := maximum hi (neg lo)
  let widen := addUp (mulUp big w₁) (mulUp (absolute (mulUp ca cb)) w₂)
  (offset, addUp (addUp (half (subUp hi lo)) (subUp offsetUp offset)) widen)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
