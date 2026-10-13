import CORALean.ContDynamics.LinearSys.Definitions.VerifyIter
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope
import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# `Alg. 3` lines 3-25: one iteration of the main loop

`verifyStep`: [1, Alg. 3]. Recompute the outer- and inner-approximation at the current
`ε_max` (lines 3-4), run `Prop. 7`'s containment check against every safe set and `Prop.
8`'s intersection check against every unsafe set (lines 5-17), then shrink `ε_max` (lines
18-25).

Lines 3-4, 7, 9, 13, 15 are call-outs in `[1]` itself — "comp. with Alg. 2", "see Sec. V",
"see (46)/(45)", "see Prop. 8" — none inlined there either, so `reachFn`, `innerApprox`,
`distG`, `distF` stand for them here too, `Zonotope.conZonotope` letting one `distG`/`distF`
pair cover eq. (46)'s zonotope case and eq. (45)'s general one; no solver is invented for
either, matching this page's `Prop. 7`/`Prop. 8` findings. `sys`, `X₀`, `U`, `t_end` enter only
through `reachFn`. `r + 1`/`w + 1` keep both set families nonempty, as `for j ← 1 to r` already
presumes.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
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
  let Rout := reachFn εmax                                                    -- 3. R̂(t)
  let Rin := innerApprox Rout εmax                                            -- 4. Ř(t), Sec. V
  let νGout := Finset.univ.sup' Finset.univ_nonempty
    (fun j => distG Rout.conZonotope (G j))                                   -- 5.-8. ν̂_G
  let νGin := Finset.univ.sup' Finset.univ_nonempty
    (fun j => distG Rin (G j))                                                -- 5., 9.-10. ν̌_G
  let νFout := Finset.univ.inf' Finset.univ_nonempty
    (fun j => distF Rout.conZonotope (F j))                                   -- 5., 12.-14. ν̂_F
  let νFin := Finset.univ.inf' Finset.univ_nonempty
    (fun j => distF Rin (F j))                                                -- 5., 12., 15.-16.
  let ν0 := min (-νGin) νFin                                                  -- 18.
  let ν1 := if le 0 νGout then min ν0 νGout else ν0                           -- 19.-21.
  let ν2 := if le νFout 0 then min ν1 (-νFout) else ν1                        -- 22.-24.
  let εmax' := max (0.1 * εmax) (min ν2 (0.9 * εmax))                         -- 25.
  ({ νGout := νGout, νGin := νGin, νFout := νFout, νFin := νFin }, εmax')

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
