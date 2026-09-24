import CORALean.NN.Definitions.MergeBucket
import CORALean.NN.Operations.DynamicMergeBuckets
import CORALean.NN.Operations.StaticMergeBuckets

/-!
# Initialising a layer's merge buckets

[1, Alg. 1]'s "initialize merge buckets `B_{k,δ}`", whichever of [1]'s two ways (Sec. 3.2)
the layer's `MergeBuckets` names: `staticMergeBuckets` at stored values, `dynamicMergeBuckets`
at the neurons' centres.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- "Initialize merge buckets `B_{k,δ}`", whichever way (Sec. 3.2) the layer names. -/
def initMergeBuckets (le : 𝕋 → 𝕋 → Bool) : MergeBuckets 𝕋 → Interval (Vec 𝕋 n) → 𝕋 → Fin n → Bool
  | .static ys => staticMergeBuckets le ys
  | .dynamic => dynamicMergeBuckets le

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
