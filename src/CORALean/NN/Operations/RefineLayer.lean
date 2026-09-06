import CORALean.NN.Operations.Raise

/-!
# The layer-wise refinement step

[1, Def. 4.6]: every neuron of layer `l` moves up an order at once, which by
[1, Lemma 4.3] costs no generators beyond what the layer's largest order
already spends. One `raise` at every coordinate.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One layer-wise step [1, Def. 4.6]: every neuron of layer `l` moves up an
order at once, which by [1, Lemma 4.3] costs no generators. -/
def Schedule.refineLayer (sch : Schedule) (l : ℕ) : Schedule :=
  Schedule.raise sch l fun _ => 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
