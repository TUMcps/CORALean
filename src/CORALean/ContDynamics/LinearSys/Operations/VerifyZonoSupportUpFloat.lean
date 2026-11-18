module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifyZono
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `LinearSys.verifyZonoSupportUpFloat`, the support of a zonotope with a box from above

An upper bound of `ℓ' x` over the points `x = c + Σⱼ βⱼ gⱼ + e` of a `LinearSys.VerifyZono`, for
every direction `ℓ` within `w` of the float `ℓ̃` entrywise: `ℓ̃'c + Σⱼ |ℓ̃'gⱼ| + |ℓ̃|'r`, the error
`w'μ` with `μ ≥ |c| + Σⱼ |gⱼ| + r` the magnitude of the set, every operation rounded up. The
generators are summed in their order. For `w = 0` the error term is `0`.

## Inputs
* `Z` – float zonotope with a box
* `ℓ` – float direction
* `w` – float bound of the entrywise error of the direction

## Output
* float upper bound of the support of `Z` along every direction within `w` of `ℓ`
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ℓ̃'c + Σⱼ |ℓ̃'gⱼ| + |ℓ̃|'r + w'μ`, rounded up. -/
def LinearSys.verifyZonoSupportUpFloat (Z : LinearSys.VerifyZono 𝕋 q) (ℓ w : Vec 𝕋 q) : 𝕋 :=
  let gs := Z.G.foldl (fun acc g =>                                    -- Σⱼ |ℓ̃'gⱼ|
    addUp acc (maximum (absolute (dotUp ℓ g)) (absolute (dotDown ℓ g)))) zero
  let μ := fun i => addUp (addUp (absolute (Z.c i))                    -- ≥ |cᵢ| + Σⱼ |gⱼᵢ| + rᵢ
    (Z.G.foldl (fun acc g => addUp acc (absolute (g i))) zero)) (Z.r i)
  addUp (addUp (addUp (dotUp ℓ Z.c) gs) (dotUp (fun i => absolute (ℓ i)) Z.r)) (dotUp w μ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
