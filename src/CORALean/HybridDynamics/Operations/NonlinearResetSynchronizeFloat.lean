module

public import CORALean.HybridDynamics.Definitions.NonlinearResetFloatModel
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `NonlinearReset.synchronize` for float models

CORA's `nonlinearReset/synchronize` on the interval extensions of the component resets:
`f = Σ f_i(x, u) + x(idStates)`, the sum of the component boxes plus the pre-jump box at the
coordinates `idStates`, each sum rounded outward (`sumDown`, `sumUp`; the added box is exact).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NonlinearReset.FloatModel.synchronize (fms : Fin k → NonlinearReset.FloatModel 𝕋 n m n)
    (idStates : Finset (Fin n)) : NonlinearReset.FloatModel 𝕋 n m n where
  f := fun X U =>
    ⟨fun i => addDown (if i ∈ idStates then X.inf i else zero)
        (sumDown fun j => ((fms j).f X U).inf i),
     fun i => addUp (if i ∈ idStates then X.sup i else zero)
        (sumUp fun j => ((fms j).f X U).sup i)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
