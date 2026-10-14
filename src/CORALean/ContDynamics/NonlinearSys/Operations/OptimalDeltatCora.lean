module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# `optimalDeltatCora`, CORA's `aux_optimaldeltat`

The time step size CORA's `@nonlinearSys/linReach_adaptive.m` tunes (`aux_optimaldeltat`, at
`alg = 'lin'`), line by line: the candidates `deltat * mu^k'` for `k' = 0, …, kprimemax`, the
estimate `objfuncset` of the set size after the finite horizon (eq. (57) of [1]), and its first
minimizer, `min`'s index. `rR` and `rerr1` are the radii the caller reads from `Rt` and `Rerr`;
`mu` is `opt.decrFactor`, `redFactor` is `opt.redFactor`.

This is the code, not [1]'s §5.4 (`optDeltat`, a descent that stops at the first increase): MATLAB's
`min` scans every candidate. The first minimizer is a left fold that moves only on a strict
decrease.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `aux_optimaldeltat` at `alg = 'lin'`: the candidate time step size whose estimated
set size after the finite horizon `deltat` is smallest, the first one on ties. -/
noncomputable def NonlinearSys.optimalDeltatCora
    (rR rerr1 deltat varphimin zetaP mu redFactor : ℝ) : ℝ :=
  let dHused : ℝ := 1 / 2                                 -- dHused = 0.5 ('lin')
  let zetaZ := redFactor * dHused                         -- zetaZ = opt.redFactor * dHused
  let kprimemax := ⌈-Real.log 100 / Real.log mu⌉₊         -- kprimemax = ceil(-log(100)/log(mu))
  let kprime := List.range (kprimemax + 1)                -- kprime = 0:round(kprimemax)
  let k := fun j : ℕ => mu ^ (-(j : ℤ))                   -- k = mu .^ (-kprime)
  let deltats := fun j : ℕ => deltat * mu ^ j             -- deltats = deltat * mu.^kprime
  let floork := fun j : ℕ => ⌊k j⌋₊                       -- floork = floor(k)
  let varphimax := mu                                     -- varphimax = mu
  let varphi_h := varphimax - varphimin                   -- varphi_h = (varphimax - varphimin)
  let varphi := fun j : ℕ =>                              -- varphi = (varphimin + (deltats(1)
    (varphimin + (deltats 0 - deltats j) / deltats 0      --   - deltats)/deltats(1)
      * varphi_h) / mu                                    --   * varphi_h) / mu
  let varphiprod := fun j : ℕ =>                          -- varphiprod = cumprod(varphi)
    ∏ i ∈ Finset.range (j + 1), varphi i
  let sumallbutlast := fun j : ℕ =>                       -- sumallbutlast(i) = sum(
    ∑ i ∈ Finset.Icc 1 (floork j),                        --   (1:floork(i)) terms of
      (1 + 2 * zetaZ) ^ (k j + 1 - (i : ℝ))               --   firstfactor .*
        * zetaP ^ (1 - (i : ℝ) / k j)                     --   secondfactor)
  let objfuncset := fun j : ℕ =>                          -- objfuncset =
    rR * (1 + 2 * zetaZ) ^ (k j) * zetaP                  --   rR*(1+2*zetaZ).^k*zetaP
      + rerr1 / k j * varphiprod j                        --   + rerr1./k.*varphiprod.*
        * (sumallbutlast j                                --   (sumallbutlast + (1+zetaZ)
          + (1 + zetaZ) ^ (k j - (j : ℝ))                 --   .^(k-kprime)
            * (k j - (floork j : ℝ)))                     --   .*(k-floork))
  let bestIdxnew := kprime.foldl                          -- [~,bestIdxnew] = min(objfuncset)
    (fun b j => if objfuncset j < objfuncset b then j else b) 0
  deltats bestIdxnew                                      -- deltatest = deltats(bestIdxnew)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
