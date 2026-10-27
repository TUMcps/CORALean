module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Operations.MulHi

@[expose] public section

/-!
# `Zonotope.halfspaceRange`, over a floating-point scalar

`Real.Zonotope.halfspaceRange`, [1, Sec. 5.2]: `[ω̲, ω̄]`, the range of `nᵀx − d` over `Z`. The
center's `nᵀc − d` is bracketed by `dotDown`/`dotUp` and the directed differences, the
generators' `∑ⱼ |nᵀgⱼ|` is rounded up from `max(⌈nᵀgⱼ⌉, −⌊nᵀgⱼ⌋)`, and the error box adds
`∑ᵢ nᵢeᵢ`, each `nᵢeᵢ` between the corner products of `nᵢ` and `[E̲ᵢ, Ēᵢ]`.

## Inputs
* `nv` – halfspace normal
* `d` – halfspace offset
* `Z` – zonotope

## Output
* range of the halfspace function over the zonotope, rounded outward

## References

* [1] [M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control,
      2012.](../../../../../../references/2012/althoff-hscc-avoiding-intersection.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 5.2]: `[ω̲, ω̄]`, the range of `nᵀx − d` over `Z`, rounded outward. -/
def Zonotope.halfspaceRange (nv : Vec 𝕋 n) (d : 𝕋) (Z : Zonotope (Vec 𝕋 n)) : Interval 𝕋 :=
  let ωcLo := subDown (dotDown nv Z.c) d                  -- the center `nᵀc − d`, down
  let ωcHi := subUp (dotUp nv Z.c) d                      -- and up
  let ρ := sumUp fun j =>                                 -- `∑ⱼ |nᵀgⱼ|`, up
    maximum (dotUp nv (Z.G j)) (neg (dotDown nv (Z.G j)))
  -- `nᵀe`
  let eLo := sumDown fun i => Interval.mulLo (nv i) (nv i) (Z.I_error.inf i) (Z.I_error.sup i)
  let eHi := sumUp fun i => Interval.mulHi (nv i) (nv i) (Z.I_error.inf i) (Z.I_error.sup i)
  ⟨addDown (subDown ωcLo ρ) eLo, addUp (addUp ωcHi ρ) eHi⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
