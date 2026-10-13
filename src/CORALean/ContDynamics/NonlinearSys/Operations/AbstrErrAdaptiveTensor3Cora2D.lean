import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-!
# `abstrErrAdaptiveTensor3Cora2D`, `priv_abstractionError_adaptive` at `tensorOrder = 3`

CORA's `@nonlinearSys/private/priv_abstractionError_adaptive.m`, `alg = 'lin'`,
`tensorOrder = 3` branch (l. 110-199), in two dimensions without inputs, line by line: `H` the
Hessian at `p`, `dz = IH_x`, `errorSec = 0.5 * quadMap(Z,H)`, `[T,ind]` the tensor file over
`totalInt_x`, and the remainder loop as printed (l. 168-172): the tensor is `T{i,ind{i}(j)}`
but the factor is `dz(j)`, the position `j`, not the column `ind{i}(j)`. An all-empty `ind` gives
`errorLagr = 0`. Sets are interval hulls `(inf, sup)` per coordinate; `err` is
`abs(center) + sum(abs(generators))` of `VerrorDyn`, i.e. `max |inf| |sup|` of its hull.

`quad dz M` is the interval `dz.'*M*dz`, `imul` the interval product, `qmap` the hull of
`quadMap(Z,H)` for `Z` the reduced `R`, `red` the hull of `reduce(VerrorDyn,'adaptive',…)`:
all arguments (the order reductions are not modelled; the zonotope is its hull, exact for a
box `VerrorDyn`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `priv_abstractionError_adaptive` (`'lin'`, `tensorOrder = 3`) in 2D without inputs:
the returned `err` for the box `Rmax` and linearization point `p`. -/
noncomputable def NonlinearSys.abstrErrAdaptiveTensor3Cora2D
    (hess : (Fin 2 → ℝ) → Fin 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (T : (Fin 2 → ℝ × ℝ) → Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) (ℝ × ℝ))
    (ind : Fin 2 → List (Fin 2))
    (quad : (Fin 2 → ℝ × ℝ) → Matrix (Fin 2) (Fin 2) (ℝ × ℝ) → ℝ × ℝ)
    (imul : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (qmap : (Fin 2 → ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ → ℝ × ℝ)
    (red : (Fin 2 → ℝ × ℝ) → Fin 2 → ℝ × ℝ)
    (p : Fin 2 → ℝ) (Rmax : Fin 2 → ℝ × ℝ) : Fin 2 → ℝ :=
  let IH_x := Rmax                                        -- IH_x = interval(R)
  let totalInt_x : Fin 2 → ℝ × ℝ := fun k => ((IH_x k).1 + p k, (IH_x k).2 + p k) -- IH_x + p.x
  let H := hess p                                         -- H = nlnsys.hessian(p.x,p.u)
  let dz := IH_x                                          -- dz = [IH_x; IH_u]
  let errorSec : Fin 2 → ℝ × ℝ := fun i =>                -- errorSec = 0.5 * quadMap(Z,H)
    ((1 / 2) * (qmap dz (H i)).1, (1 / 2) * (qmap dz (H i)).2)
  let Tx := T totalInt_x                                  -- [T,ind] = thirdOrderTensor(totalInt)
  let errorLagr : Fin 2 → ℝ × ℝ :=
    if (ind 0 ++ ind 1).isEmpty then fun _ => (0, 0)      -- ind empty: errorLagr = 0
    else fun i =>                                         -- for i=1:length(ind)
      let error_sum := (List.range (ind i).length).foldl  -- for j=1:length(ind{i})
        (fun s (j : ℕ) =>
          let error_tmp := quad dz (Tx i ((ind i).getD j 0)) -- dz.'*T{i,ind{i}(j)}*dz
          let e := imul error_tmp (dz (Fin.ofNat 2 j))    -- error_tmp * dz(j)
          (s.1 + e.1, s.2 + e.2)) (0, 0)                  -- error_sum = error_sum + ...
      ((1 / 6) * error_sum.1, (1 / 6) * error_sum.2)      -- errorLagr(i,1) = 1/6*error_sum
  let VerrorDyn : Fin 2 → ℝ × ℝ := fun i =>               -- VerrorDyn = errorSec + errorLagr
    ((errorSec i).1 + (errorLagr i).1, (errorSec i).2 + (errorLagr i).2)
  let VerrorDyn' := red VerrorDyn                         -- reduce(VerrorDyn,'adaptive',…)
  fun i => max |(VerrorDyn' i).1| |(VerrorDyn' i).2|      -- err = abs(center)+sum(abs(gens))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
