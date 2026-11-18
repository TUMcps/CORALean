module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `LinearSys.verifyInputOuterFloat`, the support of one step's varying input from above

CORA's `aux_overPU` keeps the generators `Δt^{i+1}/(i+1)! Aⁱ M` of every order `i < η`, each with
its own factors, and the support of the step's varying input along `ℓ` is `Σᵢ Σ_c |ℓ' Pᵢ M_c|`.
Here every `Pᵢ M` is a box of `V`, the remainder past them is at most `ρ_l` in row `l`, and the
direction is within `E` of `ℓ̃`: `Σᵢ Σ_c |ℓ̃' [Pᵢ M]_c| + |ℓ̃|'ρ + E β`, each `|ℓ̃' [Pᵢ M]_c|` the
magnitude of its sums rounded up and down, `β` a bound of the scaled row sums of all of it.

## Inputs
* `V` – float boxes of the orders
* `ρ` – float bound of the remainder per row
* `β` – float bound of the scaled row sums of the orders and the remainder
* `ℓ` – float direction
* `E` – float bound of the weighted error of the direction

## Output
* float upper bound of the support of one step's varying input along the exact direction
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `|ℓ̃' X_c|` over the box, from above: the magnitude of the sums rounded up and down. -/
@[step_of LinearSys.verifyInputOuterFloat]
def LinearSys.step_verifyBoxDotAbsFloat (X : Interval (Mat 𝕋 n m)) (ℓ : Vec 𝕋 n) (c : Fin m) : 𝕋 :=
  let up := sumUp fun l => maximum (mulUp (ℓ l) (X.inf l c)) (mulUp (ℓ l) (X.sup l c))
  let dn := sumDown fun l => minimum (mulDown (ℓ l) (X.inf l c)) (mulDown (ℓ l) (X.sup l c))
  maximum (absolute up) (absolute dn)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Σᵢ Σ_c |ℓ̃' Vᵢ_c| + |ℓ̃|'ρ + E β`, rounded up, the orders added in their order. -/
def LinearSys.verifyInputOuterFloat (V : List (Interval (Mat 𝕋 n m))) (ρ : Vec 𝕋 n) (β : 𝕋)
    (ℓ : Vec 𝕋 n) (E : 𝕋) : 𝕋 :=
  let t₁ := V.foldl (fun acc X => addUp acc
    (sumUp fun c => LinearSys.step_verifyBoxDotAbsFloat X ℓ c)) zero            -- Σᵢ Σ_c |ℓ̃' Vᵢ_c|
  let t₂ := sumUp fun l => mulUp (absolute (ℓ l)) (ρ l)                      -- |ℓ̃|'ρ
  addUp (addUp t₁ t₂) (mulUp E β)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
