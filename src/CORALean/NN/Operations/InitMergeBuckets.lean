module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.NN.Definitions.IsInMergeBucket
public import CORALean.NN.Operations.Bucketed
public import CORALean.Global.StepOf

@[expose] public section

/-!
# Initialising a layer's merge buckets

[1, Alg. 1]'s "initialize merge buckets `B_{k,δ}`", whichever of [1]'s two ways (Sec. 3.2) the
layer's `MergeBuckets` names: `step_staticMergeBuckets` at stored values, `step_dynamicMergeBuckets`
at the neurons' centers.

## Inputs
* `le` – comparison of two scalars

## Output
* mask of the merged neurons for the chosen initialisation

## References

* [1] [T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for Formal Verification".
      Transactions on Machine Learning Research,
      2025.](../../../../references/2023/ladner-tmlr-network-reduction.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- [1, Def. 3]'s `I_k(i) ⊆ [y - δ, y + δ]`, decided by `le`. -/
@[step_of initMergeBuckets]
def step_inMergeBucket (le : 𝕋 → 𝕋 → Bool) (I : Interval (Vec 𝕋 n)) (y δ : 𝕋) (i : Fin n) : Bool :=
  le (subDown y δ) (I.inf i) && le (I.sup i) (addUp y δ)

/-- [1, Eq. 6]'s dynamic buckets, one at each neuron's center in turn, kept disjoint by
skipping the neurons already merged and used only when they hold two or more. -/
@[step_of initMergeBuckets]
def step_dynamicMergeBuckets (le : 𝕋 → 𝕋 → Bool) (I : Interval (Vec 𝕋 n)) (δ : 𝕋) : Fin n → Bool :=
  Fin.foldl n (fun merged j =>
      let c := half (addUp (I.inf j) (I.sup j))                     -- [1, Eq. 6]'s `c(j)`
      let B_cδ := fun i => !merged i && step_inMergeBucket le I c δ i    -- `B_{k,c(j),δ}`, disjoint
      if 2 ≤ bucketed B_cδ then fun i => merged i || B_cδ i else merged)  -- used if not a singleton
    fun _ => false

/-- [1, Eq. 5]'s static buckets `B_{k,y,δ}`, one per asymptotic value `y`: a neuron is merged
when one of them holds it, and belongs to the first that does. -/
@[step_of initMergeBuckets]
def step_staticMergeBuckets (le : 𝕋 → 𝕋 → Bool) (ys : List 𝕋) (I : Interval (Vec 𝕋 n)) (δ : 𝕋) :
    Fin n → Bool :=
  fun i => ys.any fun y => step_inMergeBucket le I y δ i


-- =====================================  MAIN DEFINITION  ====================================== --

/-- "Initialize merge buckets `B_{k,δ}`", whichever way (Sec. 3.2) the layer names. -/
def initMergeBuckets (le : 𝕋 → 𝕋 → Bool) : MergeBuckets 𝕋 → Interval (Vec 𝕋 n) → 𝕋 → Fin n → Bool
  | .static ys => step_staticMergeBuckets le ys
  | .dynamic => step_dynamicMergeBuckets le

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
