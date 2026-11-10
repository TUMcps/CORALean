module

public import CORALean.Global.Float.Log
public import CORALean.Global.Float.PowUp

@[expose] public section

/-!
# `aux_varphitotal` of CORA's `linReach_adaptive`, in floats

The total scaling of the abstraction error between two time step sizes CORA's
`linReach_adaptive.m` estimates, line by line: the number of `decrFactor` scalings from the
current to the previous step size, `nrScalings = log(prev/curr)/log(decrFactor)`, the gains
interpolated linearly between `varphi` at the current step and `varphi_lim` at zero for each whole
scaling (extrapolated, and inverted, when the current step is the larger), the last one corrected
for the partial scaling, and their product. `10*eps` is `10 · 2⁻⁵²`. A tuning heuristic.

## Inputs
* `p` – precision of `log`
* `varphi` – gain at the current step size
* `varphi_lim` – gain at zero
* `prev` – previous time step size
* `curr` – current time step size
* `decr` – `decrFactor`

## Output
* the total scaling
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `aux_varphitotal`: the product of the interpolated gains from `curr` to `prev`. -/
def NonlinearSys.varphiTotalFloat (p : ℕ) (varphi varphi_lim prev curr decr : 𝕋) : 𝕋 :=
  let nrScalings := divUp (logUp p p (divUp prev curr)) (logUp p p decr)  -- log(prev/curr)/log(d)
  let eps10 := mulUp (nsmulUp 10 one) (Nat.iterate half 52 one)      -- 10*eps
  let dpow := fun (i : ℤ) =>                                        -- decrFactor^i
    if 0 ≤ i then powUp decr i.toNat else divUp one (powUp decr (-i).toNat)
  let interp := fun (i : ℤ) =>                                      -- varphi + (lim - varphi)
    addUp varphi (mulUp (subUp varphi_lim varphi)                   --   * (curr - d^i curr)
      (divUp (subUp curr (mulUp (dpow i) curr)) curr))              --   / (curr - 0)
  let lastCorr := fun (last : 𝕋) (low high : ℤ) =>                   -- varphis(end) + (1 - ..)
    addUp last (mulUp (subUp one last)                              --   * (prev - curr d^high)
      (divUp (subUp prev (mulUp curr (dpow high)))                  --   / (curr (d^low
        (mulUp curr (subUp (dpow low) (dpow high)))))               --   - d^high))
  if le nrScalings zero = false then                                -- nrScalings > 0
    let low : ℤ := ⌊ToRat.toRat (addUp nrScalings eps10)⌋           -- floor(nrScalings + 10eps)
    let vs := varphi :: (List.range low.toNat).map fun i => interp (i + 1)  -- i = 1:low
    let vs := vs.dropLast ++ [lastCorr (vs.getLastD varphi) low (low + 1)]
    vs.foldl mulUp one                                              -- prod(varphis)
  else
    let low : ℤ := ⌈ToRat.toRat (subUp nrScalings eps10)⌉           -- ceil(nrScalings - 10eps)
    let vs := varphi :: (List.range (-low).toNat).map fun i => interp (-(i + 1 : ℤ))  -- -1:-1:low
    let vs := vs.dropLast ++ [lastCorr (vs.getLastD varphi) low (low - 1)]
    (vs.map fun v => divUp one v).foldl mulUp one                   -- prod(1 ./ varphis)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
