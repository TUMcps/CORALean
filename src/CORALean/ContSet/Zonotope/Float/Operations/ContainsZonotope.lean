module

public import CORALean.ContSet.Zonotope.Float.Operations.BallB
public import CORALean.ContSet.Zonotope.Float.Operations.BallCert
public import CORALean.ContSet.Zonotope.Float.Operations.Basic
public import CORALean.Global.Float.FloatOps
public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Zonotope.containsZonotope`, over a floating-point scalar

CORA's `'approx:st'` containment (Sadraddini and Tedrake): `Z₁ ⊆ Z₂` if `G₁ = G₂ Γ`,
`c₁ - c₂ = G₂ β₀` and the row sums of `|Γ|` plus `|β₀|` are at most one. Rounding cannot confirm the
equalities, so approximate `Γ = H G₁` and `β₀ = H (c₁ - c₂ - e₂)` are formed with a right inverse
`H` of `G₂` the caller proposes, and what they leave over is absorbed: the residuals and the first
set's error box must fit in the box of radius `B` that `Zonotope.ballCert` reaches with coefficients
of size at most `δ`, and `|β₀ₖ| + ∑ⱼ |Γₖⱼ| + δ` must stay at most one. `e₂` is the second error
box's lower corner (the box must be nonempty); `δ` is half the slack. `true` proves `Z₁ ⊆ Z₂`;
`false` refutes nothing.

## Inputs
* `Z₂` – outer zonotope
* `Z₁` – inner zonotope
* `H` – candidate right inverse of the outer generators

## Output
* true when the inner zonotope is certified inside the outer
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

@[step_of Zonotope.containsZonotope]
def Zonotope.step_mulResidual {m h : ℕ} (A : Mat 𝕋 n m) (G : Mat 𝕋 n h) (Γ : Mat 𝕋 h m) :
    Fin n → Fin m → 𝕋 := fun i j =>
  maximum (absolute (subDown (A i j) (dotUp (fun l => G i l) fun l => Γ l j)))
    (absolute (subUp (A i j) (dotDown (fun l => G i l) fun l => Γ l j)))

@[step_of Zonotope.containsZonotope]
def Zonotope.step_errBound (E : Interval (Vec 𝕋 n)) : Vec 𝕋 n := fun i =>
  maximum (absolute (E.inf i)) (absolute (E.sup i))

@[step_of Zonotope.containsZonotope]
def Zonotope.step_entryDeviation (x e lo hi : Vec 𝕋 n) (i : Fin n) : 𝕋 :=
  maximum (subUp (subUp (x i) (e i)) (lo i)) (subUp (hi i) (subDown (x i) (e i)))

/-- Entry `i` of what the rounded `β` (`stBeta`) and `Γ` (`stGamma`) of the `'approx:st'` test
(`st`: Sadraddini-Tedrake) leave over, rounded up: the center and generator residuals of
`c₂ - c₁ = G₂ β`, `G₁ = G₂ Γ`, plus `Z₁`'s error box. The box of `ballCert` must absorb it. -/
@[step_of Zonotope.containsZonotope]
def Zonotope.step_stLeftover (Z₂ Z₁ : Zonotope (Vec 𝕋 n)) (H : Mat 𝕋 Z₂.h n) (i : Fin n) : 𝕋 :=
  addUp (addUp
    (Zonotope.step_entryDeviation Z₁.c Z₂.I_error.inf (Z₂.pointLo (Z₂.stBeta Z₁ H))
      (Z₂.pointHi (Z₂.stBeta Z₁ H)) i)
    (sumUp fun j => Zonotope.step_mulResidual (fun i j => Z₁.G j i) (fun i j => Z₂.G j i)
      (Z₂.stGamma Z₁ H) i j))
    (Zonotope.step_errBound Z₁.I_error i)


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.containsZonotope (Z₂ Z₁ : Zonotope (Vec 𝕋 n)) (H : Mat 𝕋 Z₂.h n) : Bool :=
  let δ := Z₂.stDelta Z₁ H
  Zonotope.ballCert (fun i j => Z₂.G j i) H (Zonotope.ballB H δ) δ
    && (List.finRange Z₂.h).all (fun k => le (addUp (Z₂.stUsed Z₁ H k) δ) one)
    && (List.finRange n).all (fun i => le (Z₂.step_stLeftover Z₁ H i) (Zonotope.ballB H δ))
    && (List.finRange n).all fun i => le (Z₂.I_error.inf i) (Z₂.I_error.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
