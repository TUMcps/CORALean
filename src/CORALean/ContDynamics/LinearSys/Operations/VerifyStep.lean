module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifyIter
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.HPolytope.Real.HPolytope

@[expose] public section

/-!
# `Alg. 3` lines 3-25: one iteration of the main loop

`verifyStep`: [1, Alg. 3]. Recompute the outer- and inner-approximation at the current `ε_max`
(lines 3-4), run `Prop. 7`'s containment check against every safe set and `Prop. 8`'s intersection
check against every unsafe set (lines 5-17), then shrink `ε_max` (lines 18-25). Lines 3-4, 7, 9, 13,
15 are call-outs in `[1]` itself, none inlined there either, so `reachFn`, `innerApprox`, `distG`,
`distF` stand for them here too, `Zonotope.conZonotope` letting one `distG`/`distF` pair cover
eq. (46)'s zonotope case and eq. (45)'s general one; no solver is invented for either. `sys`, `X₀`,
`U`, `t_end` enter only through `reachFn`. `r + 1`/`w + 1` keep both set families nonempty, as
`for j ← 1 to r` already presumes.

## Inputs
* `reachFn` – reachable set as a function of the error
* `innerApprox` – inner approximation at an error
* `distG` – distance to a safe polytope
* `distF` – distance to an unsafe polytope
* `G` – safe polytopes
* `F` – unsafe polytopes
* `le` – comparison oracle on reals
* `εmax` – maximal error

## Output
* iteration outcome and the shrunk error for the next one

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n r w : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 3-25: one iteration of [1, Alg. 3]'s main loop, and the shrunk `ε_max` for the next
one. -/
noncomputable def LinearSys.verifyStep (reachFn : ℝ → Zonotope (Vec ℝ n))
    (innerApprox : Zonotope (Vec ℝ n) → ℝ → ConZonotope (Vec ℝ n))
    (distG distF : ConZonotope (Vec ℝ n) → HPolytope (Vec ℝ n) → ℝ)
    (G : Fin (r + 1) → HPolytope (Vec ℝ n)) (F : Fin (w + 1) → HPolytope (Vec ℝ n))
    (le : ℝ → ℝ → Bool) (εmax : ℝ) : LinearSys.VerifyIter × ℝ :=
  -- 3. R̂(t)
  let Rout := reachFn εmax
  -- 4. Ř(t), Sec. V
  let Rin := innerApprox Rout εmax
  -- 5.-8. ν̂_G
  let νGout := Finset.univ.sup' Finset.univ_nonempty
    (fun j => distG Rout.conZonotope (G j))
  -- 5. and 9.-10. ν̌_G
  let νGin := Finset.univ.sup' Finset.univ_nonempty
    (fun j => distG Rin (G j))
  -- 5. and 12.-14. ν̂_F
  let νFout := Finset.univ.inf' Finset.univ_nonempty
    (fun j => distF Rout.conZonotope (F j))
  -- 5., 12. and 15.-16. ν̌_F
  let νFin := Finset.univ.inf' Finset.univ_nonempty
    (fun j => distF Rin (F j))
  -- 18. ν ← min(-ν̌_G, ν̌_F)
  let ν0 := min (-νGin) νFin
  -- 19.-21. if ν̂_G ≥ 0, ν ← min(ν, ν̂_G)
  let ν1 := if le 0 νGout then min ν0 νGout else ν0
  -- 22.-24. if ν̂_F ≤ 0, ν ← min(ν, -ν̂_F)
  let ν2 := if le νFout 0 then min ν1 (-νFout) else ν1
  -- 25. ε_max ← max(0.1 ε_max, min(ν, 0.9 ε_max))
  let εmax' := max (0.1 * εmax) (min ν2 (0.9 * εmax))
  ({ νGout := νGout, νGin := νGin, νFout := νFout, νFin := νFin }, εmax')

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
