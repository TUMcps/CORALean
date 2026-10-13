module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifyIterFloat
public import CORALean.ContDynamics.LinearSys.Operations.MaximumFold
public import CORALean.ContDynamics.LinearSys.Operations.MinimumFold
public import CORALean.ContSet.ConZonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.HPolytope.Float.Instances
public import CORALean.ContSet.Conversion.Float.Zonotope_to_ConZonotope

@[expose] public section

/-!
# One iteration of the verification loop, in floats

Lines 3-25 of [1, Alg. 3]: the outer and inner approximations at `ε_max`, the four aggregated
distances by the exact folds `maximumFold` and `minimumFold`, and the shrunk `ε_max` for the next
iteration. `ε_max` only steers precision, so its tenth and nine tenths are rounded, in no
particular direction; no verdict depends on them.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n r w : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSys.verifyStepFloat (reachFn : 𝕋 → Zonotope (Vec 𝕋 n))
    (innerApprox : Zonotope (Vec 𝕋 n) → 𝕋 → ConZonotope 𝕋 (Vec 𝕋 n))
    (distG distF : ConZonotope 𝕋 (Vec 𝕋 n) → HPolytope 𝕋 (Vec 𝕋 n) → 𝕋)
    (G : Fin (r + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (F : Fin (w + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (εmax : 𝕋) :
    LinearSys.VerifyIterFloat 𝕋 × 𝕋 :=
  let Rout := reachFn εmax                                                    -- 3. R̂(t)
  let Rin := innerApprox Rout εmax                                            -- 4. Ř(t), Sec. V
  let νGout := LinearSys.maximumFold fun j => distG Rout.conZonotope (G j) -- 5.-8. ν̂_G
  let νGin := LinearSys.maximumFold fun j => distG Rin (G j)           -- 5., 9.-10. ν̌_G
  let νFout := LinearSys.minimumFold fun j => distF Rout.conZonotope (F j) -- 5., 12.-14. ν̂_F
  let νFin := LinearSys.minimumFold fun j => distF Rin (F j)           -- 5., 12., 15.-16.
  let ν0 := minimum (neg νGin) νFin                                           -- 18.
  let ν1 := if le zero νGout then minimum ν0 νGout else ν0                    -- 19.-21.
  let ν2 := if le νFout zero then minimum ν1 (neg νFout) else ν1              -- 22.-24.
  let ten : 𝕋 := nsmulUp 10 one
  let εmax' := maximum (divDown εmax ten)                                     -- 25.
    (minimum ν2 (subDown εmax (divDown εmax ten)))
  ({ νGout := νGout, νGin := νGin, νFout := νFout, νFin := νFin }, εmax')

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
