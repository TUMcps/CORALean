module

public import CORALean.Global.Float.Exp
public import CORALean.Global.Float.Log
public import CORALean.Global.Float.PowUp
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `aux_optimaldeltat` of CORA's `linReach_adaptive`, in floats

The step size CORA's `linReach_adaptive.m` tunes at `alg = 'lin'`, line by line: the candidates
`deltat · mu^k'`, `k' = 0, …, ⌈-log(100)/log(mu)⌉`, the estimate `objfuncset` of the set size
after the finite horizon (eq. (57) of [1]) and its first minimizer, as MATLAB's `min` scans every
candidate. The gain is interpolated from `varphimin` at the horizon to `mu` at zero; real powers are
`exp(y log x)`. A tuning heuristic, on which soundness does not depend; modelled over ℝ, to be
refuted, by `NonlinearSys.optimalDeltatCora`.

## Inputs
* `p` – precision of `exp`, `log`
* `mu` – `decrFactor`
* `redFactor` – `zeta_Z`
* `rR` – radius of the start set
* `rerr1` – radius of the abstraction error at the horizon
* `deltat` – finite horizon
* `varphimin` – gain at the horizon
* `zetaP` – exponential of the trace of `A Δt`

## Output
* the tuned time step size

## References

* [1] [M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms
      for Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems,
      2022.](../../../../../references/2022/wetzlinger-nahs-abstraction-error.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `x ^ y` for `0 < x`, as `exp(y log x)`. -/
@[step_of NonlinearSys.optimalDeltatAdaptiveFloat]
def step_rpowFloat (p : ℕ) (x y : 𝕋) : 𝕋 := expUp p (mulUp y (logUp p p x))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `aux_optimaldeltat` at `alg = 'lin'`: the candidate step size whose estimated set size
after the finite horizon `deltat` is smallest, the first one on ties. -/
def NonlinearSys.optimalDeltatAdaptiveFloat (p : ℕ)
    (mu redFactor rR rerr1 deltat varphimin zetaP : 𝕋) : 𝕋 :=
  let zetaZ := half redFactor                                       -- redFactor * dHused, 0.5
  let kprimemax := ⌈ToRat.toRat (divUp (neg (logUp p p (nsmulUp 100 one)))  -- ceil(-log(100)
    (logUp p p mu))⌉₊                                               --   / log(mu))
  let k := fun j : ℕ => divUp one (powUp mu j)                      -- k = mu .^ (-kprime)
  let deltats := fun j : ℕ => mulUp deltat (powUp mu j)             -- deltats = deltat*mu.^kprime
  let floork := fun j : ℕ => ⌊ToRat.toRat (k j)⌋₊                    -- floork = floor(k)
  let varphi_h := subUp mu varphimin                                -- varphimax - varphimin
  let varphi := fun j : ℕ => divUp (addUp varphimin                 -- (varphimin + (deltats(1)
    (mulUp (divUp (subUp (deltats 0) (deltats j)) (deltats 0)) varphi_h)) mu  -- - deltats)/..)/mu
  let varphiprod := fun j : ℕ =>                                    -- cumprod(varphi)
    (List.range (j + 1)).foldl (fun acc i => mulUp acc (varphi i)) one
  let a := addUp one (addUp zetaZ zetaZ)                            -- 1 + 2*zetaZ
  let sumallbutlast := fun j : ℕ =>                                 -- sum(firstfactor .*
    (List.range (floork j)).foldl (fun acc i =>                     --   secondfactor)
      let ii : 𝕋 := nsmulUp (i + 1) one
      addUp acc (mulUp (step_rpowFloat p a (subUp (addUp (k j) one) ii))
        (step_rpowFloat p zetaP (subUp one (divUp ii (k j)))))) zero
  let objfuncset := fun j : ℕ =>                                    -- objfuncset
    addUp (mulUp (mulUp rR (step_rpowFloat p a (k j))) zetaP)       --   rR*(1+2zZ).^k*zetaP
      (mulUp (mulUp (divUp rerr1 (k j)) (varphiprod j))             --   + rerr1./k.*varphiprod
        (addUp (sumallbutlast j)                                    --   .*(sumallbutlast +
          (mulUp (step_rpowFloat p (addUp one zetaZ) (subUp (k j) (nsmulUp j one)))  -- (1+zZ)
            (subUp (k j) (nsmulUp (floork j) one)))))               --   .^(k-kprime).*(k-floork))
  let best := (List.range (kprimemax + 1)).foldl (fun (b : ℕ × 𝕋) j =>  -- [~,bestIdx] = min(..)
    let o := objfuncset j
    if le b.2 o then b else (j, o)) (0, objfuncset 0)
  deltats best.1                                                    -- deltats(bestIdx)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
