module

public import CORALean.ContSet.ContSet.Operations.ProjectOnHyperplaneFloat
public import CORALean.ContSet.Conversion.Float.Interval_to_ContSet
public import CORALean.ContSet.Conversion.Float.Zonotope_to_HPolytope
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.HybridDynamics.Definitions.Location

@[expose] public section

/-!
# `Location.checkFlowFloat`

CORA's `checkFlow` for a linear flow `ẋ = A x + u`, `u ∈ U`, at float zonotopes. Each reach set is
projected onto the guard hyperplane `{x | c·x = d}` (`projectOnHyperplaneFloat`, `c` the unit
normal pointing out of the invariant); it is kept if the flow at the projection's centre
points out (`c·(A m + u_c) > 0`, evaluated in plain float arithmetic, which can only keep a
set), or else if the rounded-up support function of the flow set `A·proj ⊞ U` along `c` is not
certified `≤ 0`. Only a set that is certified to have no outward flow is dropped.

CORA bounds the flow over the projection reduced by `'pca'` to a box (and rotated by
`gramSchmidt`); the box encloses the projection, so CORA's supremum is no smaller and it keeps at
least what this keeps. The orientation of the normal by the invariant (`aux_adaptGuard`) is the
caller's.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {G : ℕ → Type}
  [∀ n, ContSet (G n) (Vec ℝ n)] {L : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reach sets `Rs` that are not certified to have no outward flow on their projection. -/
def Location.checkFlowFloat (ℓ : Location (fun k => Zonotope (Vec 𝕋 k)) G L 𝕋 n)
    (c : Vec 𝕋 n) (d : 𝕋)
    (Rs : List (Zonotope (Vec 𝕋 n))) : List (Zonotope (Vec 𝕋 n)) :=
  Rs.filter fun R =>
    -- project the reach set onto the hyperplane
    let Rproj := ContSet.projectOnHyperplaneFloat (S := fun k => Zonotope (Vec 𝕋 k)) R c d
    -- fast check: the flow at the centre of the projection, with the centre input
    let m := ScalarCentre.centreVec (S := fun k => Zonotope (Vec 𝕋 k)) Rproj
    let uc := ScalarCentre.centreVec (S := fun k => Zonotope (Vec 𝕋 k)) ℓ.U
    let flowC := sumUp fun i =>
      mulUp (c i) (addUp (sumUp fun j => mulUp (ℓ.dynamics.A i j) (m j)) (uc i))
    -- the flow set `A proj ⊞ U`, bounded from above along `c`
    let flowSet := Plus.plus
      (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := fun k => Zonotope (Vec 𝕋 k)) ℓ.dynamics.A Rproj) ℓ.U
    let flowUp := (flowSet.boundDot (c := rowLin (fun _ : Fin 1 => c) 0) c fun _ => rfl).val
    !le flowC zero || !le flowUp zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
