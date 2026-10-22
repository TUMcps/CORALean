module

public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.Global.Partition

@[expose] public section

/-!
# Merge buckets

[1, Def. 3]'s `B_{k,y,δ}`: the neurons of a nonlinear layer `k` whose bounds `Y` fit inside `[y-δ,
y+δ]`, so replacing all of them by the single value `y` costs each at most `δ`. `mergeSplit` is the
`Partition.ofPred` bridge into the split `neuronMerging_sandwich_outer` consumes.

No hypothesis `0 ≤ δ` appears below: at a negative `δ` the bucket is merely empty,
`mergeBucket_width` holding of it vacuously. `MergeBuckets` names which of [1]'s two (Sec. 3.2)
initialisations a layer's buckets come from; [1, Alg. 1] builds them.

## Inputs
* `n` – layer width
* `Y` – bounds of the layer's neurons
* `y` – merge value
* `δ` – merge tolerance
* `i` – neuron index

## Output
* the neuron's bounds fit inside the interval around the merge value

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Def. 3]'s `B_{k,y,δ}`: the neurons whose bounds fit in `[y-δ, y+δ]`. -/
def mergeBucket {n : ℕ} (Y : Real.Interval (Vec ℝ n)) (y δ : ℝ) (i : Fin n) : Prop :=
  y - δ ≤ Y.inf i ∧ Y.sup i ≤ y + δ

/-- Membership in a merge bucket is decidable. -/
noncomputable instance mergeBucket.decidablePred {n : ℕ} (Y : Real.Interval (Vec ℝ n)) (y δ : ℝ) :
    DecidablePred (mergeBucket Y y δ) :=
  fun i => by unfold mergeBucket; infer_instance

/-- The split `neuronMerging_sandwich_outer` consumes, survivors on the left. -/
noncomputable def mergeSplit {n : ℕ} (Y : Real.Interval (Vec ℝ n)) (y δ : ℝ) :=
  Partition.ofPred (mergeBucket Y y δ)

/-- [1]'s two ways (Sec. 3.2) to initialise a layer's buckets: `static` at the activation's
asymptotic values, eq. (5) — `[0, 1]` for sigmoid, `[-1, 1]` for tanh, `[0]` for ReLU — and
`dynamic` at every neuron's own center, eq. (6). The values are stored, so either layer runs it. -/
inductive MergeBuckets (𝕂 : Type) where
  | static (ys : List 𝕂)
  | dynamic

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
