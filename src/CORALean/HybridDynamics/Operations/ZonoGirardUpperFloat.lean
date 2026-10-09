import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.ContSet.Conversion.Float.Zonotope_to_HPolytope
import CORALean.HybridDynamics.Definitions.Location

/-!
# `Location.zonoGirardUpperFloat`: the upper end of a zonotope's cut by a hyperplane

[1, Alg. 2] for one zonotope `Z` and one direction `ℓ`: the plane image `Π_{n,ℓ}(Z)` is the
zonotope `[nᵀ; ℓᵀ] Z` (`mtimes`), and its cut by the line `x = γ` is bounded above by the dual
of the linear program that [1, Alg. 3] and [1, Alg. 4] solve by scanning the sorted
generators. For every multiplier `μ`, a point `(γ, y)` of the plane image has
`y = (y - μ·γ) + μγ ≤ h(-μ, 1) + μγ`, `h` the support function, here the rounded-up
`Zonotope.boundDot`; the least bound over the slopes `μ = (gⱼ)₂/(gⱼ)₁` of the plane image's
generators (the breakpoints of the dual) and `μ = 0` is returned. Any `μ` is sound, so the
rounding of a slope costs tightness only.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An upper bound of `x·ℓ` over the states `x` of `Z` with `x·nv = γ`. -/
def Location.zonoGirardUpperFloat (Z : Zonotope 𝕋 n) (nv : Vec 𝕋 n) (γ : 𝕋) (ℓ : Vec 𝕋 n) : 𝕋 :=
  -- the plane image `Π_{n,ℓ}(Z)`, a zonogon
  let S : Zonotope 𝕋 2 :=
    Mtimes.mtimes (𝕄 := Mat 𝕋) (fun (i : Fin 2) (j : Fin n) => if i = 0 then nv j else ℓ j) Z
  -- the dual bound at the multiplier `μ`
  let dual : 𝕋 → 𝕋 := fun μ =>
    addUp (S.boundDot (c := rowLin (fun _ : Fin 1 => ![neg μ, one]) 0) ![neg μ, one]
      (fun _ => rfl)).val (mulUp μ γ)
  -- the slopes `(gⱼ)₂/(gⱼ)₁` of the generators, the dual's breakpoints
  let slope : Fin S.h → 𝕋 := fun j =>
    let a := S.G 1 j
    let b := S.G 0 j
    if le zero b then (if le b zero then zero else divUp a b) else divUp (neg a) (neg b)
  (List.finRange S.h).foldl (fun m j => minimum m (dual (slope j))) (dual zero)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
