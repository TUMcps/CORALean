module

public import CORALean.ContSet.Zonotope.Float.Operations.FacetNormal
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Zonotope.zonotopeNorm`, over a floating-point scalar

CORA's `zonotopeNorm(Z, p)`, `‖p‖_Z = min {‖γ‖∞ | G γ = p}` [1, Def. 4], ignoring the center. CORA
solves a linear program; here each direction `a` bounds it from below: `G γ = p` and `|γ_j| ≤ t`
give `|a·p| ≤ t Σ_j |a·g_j|`, quotient rounded down. The directions are the axes and the cross
products of every `n - 1` generators, the facet normals [2, Thm. 2]: for `n` independent generators
the best is `‖p‖_Z` [1, Cor. 2] up to rounding. A direction with `a·g_j = 0` for every `j`
(certified by both roundings) and `a·p ≠ 0` shows no `γ` reaches `p`: the norm is `Inf`, `none`.
Any vector is a sound direction, so a rounded normal costs tightness only.

## Inputs
* `Z` – zonotope
* `p` – point

## Output
* a lower bound on `‖p‖_Z`, or `none` where `p` is certified outside the span of the generators

## References

* [1] [A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment Problem".
      European Journal of Control,
      2021.](../../../../../../references/2021/kulmburg-ejc-zonotope-containment.md)
* [2] [M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv preprint
      arXiv:1512.02794,
      2015.](../../../../../../references/2015/althoff-arxiv-minkowski-difference.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       03-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The directions `zonotopeNorm` tries: the axes, then the cross products of `n` generators. -/
@[step_of Zonotope.zonotopeNorm]
def Zonotope.step_zonotopeNormDirs (Z : Zonotope (Vec 𝕋 (n + 1))) : List (Vec 𝕋 (n + 1)) :=
  (List.finRange (n + 1)).map (fun i k => if k = i then one else zero) ++
    ((List.finRange Z.h).sublistsLen n).attach.map fun l =>
      Z.facetNormal fun j => l.1.get ⟨j, by rw [(List.mem_sublistsLen.mp l.2).2]; exact j.isLt⟩

/-- `Σ_j |a·g_j|`, rounded up. -/
@[step_of Zonotope.zonotopeNorm]
def Zonotope.step_dirReach (Z : Zonotope (Vec 𝕋 (n + 1))) (a : Vec 𝕋 (n + 1)) : 𝕋 :=
  sumUp fun j => maximum (dotUp a (Z.G j)) (neg (dotDown a (Z.G j)))

/-- The direction `a` proves that `p` is out of reach: every generator is orthogonal to it and `p`
is not. -/
@[step_of Zonotope.zonotopeNorm]
def Zonotope.step_zonotopeNormCert (Z : Zonotope (Vec 𝕋 (n + 1))) (p a : Vec 𝕋 (n + 1)) : Bool :=
  le (Z.step_dirReach a) zero && (ltStrict zero (dotDown a p) || ltStrict (dotUp a p) zero)

/-- The lower bound `|a·p| / Σ_j |a·g_j|` the direction `a` gives, `0` where the sum is not
certified positive. -/
@[step_of Zonotope.zonotopeNorm]
def Zonotope.step_zonotopeNormAt (Z : Zonotope (Vec 𝕋 (n + 1))) (p a : Vec 𝕋 (n + 1)) : 𝕋 :=
  if ltStrict zero (Z.step_dirReach a) = true then
    maximum (divDown (dotDown a p) (Z.step_dirReach a))
      (divDown (neg (dotUp a p)) (Z.step_dirReach a))
  else zero


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `zonotopeNorm`: `none` for `+∞` (no `γ` with `G γ = p`), else a lower bound on
`‖p‖_Z`, never below `0`. -/
def Zonotope.zonotopeNorm (Z : Zonotope (Vec 𝕋 (n + 1))) (p : Vec 𝕋 (n + 1)) : Option 𝕋 :=
  if (Z.step_zonotopeNormDirs.any fun a => Z.step_zonotopeNormCert p a) = true then none
  else some (Z.step_zonotopeNormDirs.foldl
    (fun best a => maximum best (Z.step_zonotopeNormAt p a)) zero)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
