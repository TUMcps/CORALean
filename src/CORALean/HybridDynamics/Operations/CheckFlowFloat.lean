module

public import CORALean.ContSet.ContSet.Operations.ProjectOnHyperplaneFloat
public import CORALean.ContSet.Conversion.Float.Instances
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_HPolytope
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.HybridDynamics.Operations.InputSetFloat

@[expose] public section

/-!
# `Location.checkFlowFloat`

CORA's `checkFlow` for a linear flow `ẋ = A x + B u + c₀ + E w` at float zonotopes, its combined
input `inputSetFloat = B U ⊕ c₀ ⊕ E W` written `V`. Each reach set is projected onto the guard
hyperplane `{x | c·x = d}` (`projectOnHyperplaneFloat`, `c` the outward normal) and kept if the
flow at the projection's center points out, or else if the rounded-up support function of
`A·proj ⊞ V` along `c` is not certified `< 0`. CORA drops at `≤ 0`; a run that stays on the
hyperplane tangentially and jumps would be lost (`Location.mem_checkFlowFloat_of_jump`, from
`Location.IsTrajectory.not_strictly_inward`), so only a strict certificate drops. CORA's `'pca'`
box is not used, so this keeps at least what CORA keeps.

## Inputs
* `ℓ` – location
* `c` – unit normal of the guard
* `d` – guard offset
* `Rs` – reach sets

## Output
* reach sets that may flow out through the guard
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   12-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {G : ℕ → Type}
  [∀ n, ContSetLike (G n) (Vec ℝ n)] {L : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reach sets `Rs` that are not certified to have strictly inward flow on their projection. -/
def Location.checkFlowFloat (ℓ : Location 𝒵[𝕋] G L 𝕋 n)
    (c : Vec 𝕋 n) (d : 𝕋)
    (Rs : List (Zonotope (Vec 𝕋 n))) : List (Zonotope (Vec 𝕋 n)) :=
  Rs.filter fun R =>
    -- project the reach set onto the hyperplane
    let Rproj := ContSet.projectOnHyperplaneFloat (S := 𝒵[𝕋]) R c d
    -- fast check: the flow at the center of the projection, with the center input
    let m := ScalarCenter.centerVec (S := 𝒵[𝕋]) Rproj
    let uc := ScalarCenter.centerVec (S := 𝒵[𝕋]) ℓ.inputSetFloat
    let flowC := sumUp fun i =>
      mulUp (c i) (addUp (sumUp fun j => mulUp (ℓ.dynamics.A i j) (m j)) (uc i))
    -- the flow set `A proj ⊞ V`, bounded from above along `c`
    let flowSet := Plus.plus
      (Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) ℓ.dynamics.A Rproj) ℓ.inputSetFloat
    let flowUp := (flowSet.boundDot (c := Real.HPolytope.rowLin (toRealMat (fun _ : Fin 1 => c)) 0)
        c fun _ => rfl).val
    !le flowC zero || !ltStrict flowUp zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
