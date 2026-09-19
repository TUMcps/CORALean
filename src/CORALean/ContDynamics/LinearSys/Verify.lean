import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope
import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# `Alg. 3`: automated verification

[1, Alg. 3]: recompute the outer- and inner-approximation at the current `ε_max` (lines 3-4),
run `Prop. 7`'s containment check against every safe set and `Prop. 8`'s intersection check
against every unsafe set (lines 5-17), then shrink `ε_max` (lines 18-25). `verifyStep` is one
iteration, `verifyRun` the `repeat...until` of lines 2-26 with line 27's `return`, `verify`
line 1's entry point.

Lines 3-4, 7, 9, 13, 15 are call-outs in `[1]` itself — "comp. with Alg. 2", "see Sec. V",
"see (46)/(45)", "see Prop. 8" — none inlined there either, so `reachFn`, `innerApprox`,
`distG`, `distF` stand for them here too, `Zonotope.conZonotope` letting one `distG`/`distF`
pair cover eq. (46)'s zonotope case and eq. (45)'s general one; no solver is invented for
either, matching this page's `Prop. 7`/`Prop. 8` findings. `sys`, `X₀`, `U`, `t_end` enter only
through `reachFn`. `r + 1`/`w + 1` keep both set families nonempty, as `for j ← 1 to r` already
presumes. Line 1's "estimated from simulations" is left a parameter, `ε_max₀`; `[1]` gives no
bound on `Alg. 3`'s own repeat count (`Thm. 1` is about `Alg. 2`), so `verifyRun` needs `fuel`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n r w : ℕ}

/-- What one iteration of [1, Alg. 3] computes before line 25 shrinks `ε_max`: the four
distances lines 6-17 aggregate, `ν̂_G`/`ν̌_G` over the safe sets and `ν̂_F`/`ν̌_F` over the
unsafe ones. -/
structure LinearSys.VerifyIter where
  /-- `ν̂_G`, lines 6-8: the outer approximation's worst distance to leaving a safe set. -/
  νGout : ℝ
  /-- `ν̌_G`, lines 6, 9-10: the inner approximation's. -/
  νGin : ℝ
  /-- `ν̂_F`, lines 12-14: the outer approximation's worst distance to meeting an unsafe set. -/
  νFout : ℝ
  /-- `ν̌_F`, lines 12, 15-16: the inner approximation's. -/
  νFin : ℝ

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

/-- Lines 2-27: iterate `verifyStep` until the until-condition of line 26 holds, returning
line 27's verdict; `none` where `fuel` iterations were not enough. -/
noncomputable def LinearSys.verifyRun (reachFn : ℝ → Zonotope (Vec ℝ n))
    (innerApprox : Zonotope (Vec ℝ n) → ℝ → ConZonotope (Vec ℝ n))
    (distG distF : ConZonotope (Vec ℝ n) → HPolytope (Vec ℝ n) → ℝ)
    (G : Fin (r + 1) → HPolytope (Vec ℝ n)) (F : Fin (w + 1) → HPolytope (Vec ℝ n))
    (le : ℝ → ℝ → Bool) (εmax : ℝ) : ℕ → Option Bool
  | 0 => none
  | fuel + 1 =>
    let (it, εmax') :=
      LinearSys.verifyStep reachFn innerApprox distG distF G F le εmax        -- 3.-25.
    let verified := le it.νGout 0 && !(le it.νFout 0)                         -- 27. (bνG≤0)∧(bνF>0)
    let falsified := !(le it.νGin 0) || le it.νFin 0                          -- 26. (qνG>0)∨(qνF≤0)
    if verified || falsified then some verified                     -- 26. until, 27. return
    else LinearSys.verifyRun reachFn innerApprox distG distF G F le εmax' fuel -- 2. repeat


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: `true` where the specification given by the safe sets `G` and unsafe sets `F`
is verified, `false` where it is falsified, `none` where `fuel` repeat-until iterations did not
reach a verdict. -/
noncomputable def LinearSys.verify (reachFn : ℝ → Zonotope (Vec ℝ n))
    (innerApprox : Zonotope (Vec ℝ n) → ℝ → ConZonotope (Vec ℝ n))
    (distG distF : ConZonotope (Vec ℝ n) → HPolytope (Vec ℝ n) → ℝ)
    (G : Fin (r + 1) → HPolytope (Vec ℝ n)) (F : Fin (w + 1) → HPolytope (Vec ℝ n))
    (le : ℝ → ℝ → Bool) (εmax₀ : ℝ) (fuel : ℕ) : Option Bool :=
  LinearSys.verifyRun reachFn innerApprox distG distF G F le εmax₀ fuel        -- 1. ε_max ← ε_max₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
