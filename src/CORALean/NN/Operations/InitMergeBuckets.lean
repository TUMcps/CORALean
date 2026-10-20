module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.NN.Definitions.MergeBucket
public import CORALean.NN.Operations.Bucketed

@[expose] public section

/-!
# Initialising a layer's merge buckets

[1, Alg. 1]'s "initialize merge buckets `B_{k,δ}`", whichever of [1]'s two ways (Sec. 3.2) the
layer's `MergeBuckets` names: `aux_staticMergeBuckets` at stored values, `aux_dynamicMergeBuckets`
at the neurons' centers.

## Inputs
* `le` – comparison of two scalars

## Output
* mask of the merged neurons for the chosen initialisation

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- [1, Def. 3]'s `I_k(i) ⊆ [y - δ, y + δ]`, decided by `le`. -/
def aux_inMergeBucket (le : 𝕋 → 𝕋 → Bool) (I : Interval (Vec 𝕋 n)) (y δ : 𝕋) (i : Fin n) : Bool :=
  le (subDown y δ) (I.inf i) && le (I.sup i) (addUp y δ)

/-- [1, Eq. 6]'s dynamic buckets, one at each neuron's center in turn, kept disjoint by
skipping the neurons already merged and used only when they hold two or more. -/
def aux_dynamicMergeBuckets (le : 𝕋 → 𝕋 → Bool) (I : Interval (Vec 𝕋 n)) (δ : 𝕋) : Fin n → Bool :=
  Fin.foldl n (fun merged j =>
      let c := half (addUp (I.inf j) (I.sup j))                     -- [1, Eq. 6]'s `c(j)`
      let B_cδ := fun i => !merged i && aux_inMergeBucket le I c δ i    -- `B_{k,c(j),δ}`, disjoint
      if 2 ≤ bucketed B_cδ then fun i => merged i || B_cδ i else merged)  -- used if not a singleton
    fun _ => false

/-- [1, Eq. 5]'s static buckets `B_{k,y,δ}`, one per asymptotic value `y`: a neuron is merged
when one of them holds it, and belongs to the first that does. -/
def aux_staticMergeBuckets (le : 𝕋 → 𝕋 → Bool) (ys : List 𝕋) (I : Interval (Vec 𝕋 n)) (δ : 𝕋) :
    Fin n → Bool :=
  fun i => ys.any fun y => aux_inMergeBucket le I y δ i


-- =====================================  MAIN DEFINITION  ====================================== --

/-- "Initialize merge buckets `B_{k,δ}`", whichever way (Sec. 3.2) the layer names. -/
def initMergeBuckets (le : 𝕋 → 𝕋 → Bool) : MergeBuckets 𝕋 → Interval (Vec 𝕋 n) → 𝕋 → Fin n → Bool
  | .static ys => aux_staticMergeBuckets le ys
  | .dynamic => aux_dynamicMergeBuckets le

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
