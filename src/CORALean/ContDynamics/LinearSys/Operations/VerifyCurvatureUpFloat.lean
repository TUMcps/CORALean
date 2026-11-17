module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `LinearSys.verifyCurvatureUpFloat`, the support of the curvature set along a perturbed direction

Over a step, CORA's `priv_verifyRA_supportFunc` adds the support of `F X₀` along `ℓ_k`, with
`F = [F_c ± F_r]`: `ℓ'(F_c c) + Σⱼ |ℓ'(F_c gⱼ)| + |ℓ|'(F_r v)`, `v = |c| + Σⱼ |gⱼ|` (CORA takes
`|ℓ'(F_r v)|` for the last term, which can be too small; see
`LinearSys.verifySupportFuncCurvatureCora_counterexample`). The products `F_c c`, `F_c G` and
`F_r v` come as boxes and a vector computed once per step size; `E` and `βF` bound the error of the
direction and every `|(F x)ᵢ|/sᵢ` over `X₀`, as in `LinearSys.verifySupportUpFloat`.

## Inputs
* `wc` – float box of `F_c c`
* `WG` – float box of `F_c G`
* `wr` – float upper bound of `F_r v`
* `βF` – float bound of the scaled entries of `F X₀`
* `ℓ` – float direction
* `E` – float bound of the weighted error of the direction

## Output
* float upper bound of the support of `F X₀` along the exact direction
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ℓ̃'(F_c c) + Σⱼ |ℓ̃'(F_c gⱼ)| + |ℓ̃|'(F_r v) + E βF`, rounded up. -/
def LinearSys.verifyCurvatureUpFloat (wc : Interval (Vec 𝕋 n)) (WG : Interval (Mat 𝕋 n m))
    (wr : Vec 𝕋 n) (βF : 𝕋) (ℓ : Vec 𝕋 n) (E : 𝕋) : 𝕋 :=
  let t₁ := sumUp fun i => maximum (mulUp (ℓ i) (wc.inf i)) (mulUp (ℓ i) (wc.sup i)) -- ℓ̃'(F_c c)
  let gUp := fun j => sumUp fun i => maximum (mulUp (ℓ i) (WG.inf i j)) (mulUp (ℓ i) (WG.sup i j))
  let gDn := fun j => sumDown fun i =>
    minimum (mulDown (ℓ i) (WG.inf i j)) (mulDown (ℓ i) (WG.sup i j))
  let t₂ := sumUp fun j => maximum (absolute (gUp j)) (absolute (gDn j))  -- Σⱼ |ℓ̃'(F_c gⱼ)|
  let t₃ := sumUp fun i => mulUp (absolute (ℓ i)) (wr i)                   -- |ℓ̃|'(F_r v)
  addUp (addUp (addUp t₁ t₂) t₃) (mulUp E βF)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
