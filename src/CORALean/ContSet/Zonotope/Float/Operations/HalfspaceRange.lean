import CORALean.ContSet.Zonotope.Float.Zonotope
import CORALean.ContSet.Interval.Float.Operations.MulLo
import CORALean.ContSet.Interval.Float.Operations.MulHi

/-!
# `Zonotope.halfspaceRange`, over a floating-point scalar

`Real.Zonotope.halfspaceRange`, [1, Sec. 5.2]: `[ω̲, ω̄]`, the range of `nᵀx − d` over `Z`. The
centre's `nᵀc − d` is bracketed by `dotDown`/`dotUp` and the directed differences, the
generators' `∑ⱼ |nᵀgⱼ|` is rounded up from `max(⌈nᵀgⱼ⌉, −⌊nᵀgⱼ⌋)`, and the error box adds
`∑ᵢ nᵢeᵢ`, each `nᵢeᵢ` between the corner products of `nᵢ` and `[E̲ᵢ, Ēᵢ]`.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 5.2]: `[ω̲, ω̄]`, the range of `nᵀx − d` over `Z`, rounded outward. -/
def Zonotope.halfspaceRange (nv : Vec 𝕋 n) (d : 𝕋) (Z : Zonotope (Vec 𝕋 n)) : 𝕋 × 𝕋 :=
  let ωcLo := subDown (dotDown nv Z.c) d                  -- the centre `nᵀc − d`, down
  let ωcHi := subUp (dotUp nv Z.c) d                      -- and up
  let ρ := sumUp fun j =>                                 -- `∑ⱼ |nᵀgⱼ|`, up
    maximum (dotUp nv (Z.G j)) (neg (dotDown nv (Z.G j)))
  let eLo := sumDown fun i => Interval.mulLo (nv i) (nv i) (Z.E.inf i) (Z.E.sup i)  -- `nᵀe`
  let eHi := sumUp fun i => Interval.mulHi (nv i) (nv i) (Z.E.inf i) (Z.E.sup i)
  (addDown (subDown ωcLo ρ) eLo, addUp (addUp ωcHi ρ) eHi)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
