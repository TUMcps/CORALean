import CORALean.HybridDynamics.Parallel.Operations.IntervalStackProdFloat
import CORALean.HybridDynamics.Parallel.Theorems.IntervalStackProdExact

/-!
# `Interval.stackProd` over floats is the Cartesian product, exactly

The stored box denotes the exact layer's stack of the readings of the component boxes, so a point
of the stacked space is in it exactly when each of its blocks is in its component's box.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {k : ℕ} {n : Fin k → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.stackProd_exact (bs : ∀ i, Interval (Vec 𝕋 (n i))) :
    (Interval.stackProd bs).construct =
      {z | ∀ i, unstack z i ∈ (bs i).construct} := by -- --- PROOF ---
  have h : (Interval.stackProd bs).nominal =
      Real.Interval.stackProd (fun i => (bs i).nominal) := rfl
  show (Interval.stackProd bs).nominal.construct = _
  rw [h]
  exact Real.Interval.stackProd_exact (fun i => (bs i).nominal)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
