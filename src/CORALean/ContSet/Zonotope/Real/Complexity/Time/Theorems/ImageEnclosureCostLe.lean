module

public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.PlusCost
public import CORALean.ContSet.Zonotope.Real.Operations.ImageEnclosure
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ImageEnclosureCost

@[expose] public section

/-!
# `Zonotope.imageEnclosureCost_le`

[1, Prop. 15]: `O(n² q)`, at most `(cNeuron + 17) n² q` for `n, q ≥ 1`.

## Inputs
* `n` – dimension
* `q` – generator count
* `cNeuron` – cost of one neuron

## Hypotheses
* `hn` – dimension positive
* `hq` – generator count positive

## Conclusion
* image enclosure cost is at most `(cNeuron + 17) n² q`

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 15]: `O(n² q)`, at most `(cNeuron + 17) n² q` for `n, q ≥ 1`. -/
theorem Zonotope.imageEnclosureCost_le (n q : ℕ) (cNeuron : Cost) (hn : 1 ≤ n)
    (hq : 1 ≤ q) : -- --- CONCL ---
    (Zonotope.imageEnclosureCost n q cNeuron).ops ≤
      (cNeuron.ops + 17) * (n * n * q) := by -- --- PROOF ---
  simp only [Zonotope.imageEnclosureCost, Zonotope.mtimesCost, Zonotope.plusCost, Cost.matVec,
    Cost.ops_add, Cost.ops_smul]
  have h1 : n ≤ n * n * q := by nlinarith
  have h2 : n * q ≤ n * n * q := by nlinarith
  have h4 : n * n ≤ n * n * q := by nlinarith
  have h3 : n * cNeuron.ops ≤ cNeuron.ops * (n * n * q) := by nlinarith
  nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
