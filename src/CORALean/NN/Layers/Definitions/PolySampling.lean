import CORALean.NN.Layers.Definitions.EvalPoly

/-!
# The error a fit leaves, bounded by sampling over ℝ

CORA's `nnHelper/minMaxDiffOrder` [1], exactly: to bound `g = σ - p` over a box it samples,
at `N + 1` evenly spaced points, and pads by `M · (u - l) / N` for `|g'| ≤ M`. What
`ofSampling` charges, read as a function of `N` so a limit in it can be stated, and what no
bound beats — half the range `g` actually spans over the box.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `N + 1` points sampled across `[l, u]`, `i` steps of `(u - l) / N` from the left. -/
noncomputable def sampleGrid (l u : ℝ) (N : ℕ) (i : Fin (N + 1)) : ℝ :=
  l + (i : ℕ) * ((u - l) / N)

/-- The least sampled value of `g`. -/
noncomputable def sampleInf (g : ℝ → ℝ) (l u : ℝ) (N : ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i : Fin (N + 1) => g (sampleGrid l u N i)

/-- The greatest sampled value of `g`. -/
noncomputable def sampleSup (g : ℝ → ℝ) (l u : ℝ) (N : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i : Fin (N + 1) => g (sampleGrid l u N i)

/-- What sampling charges for `g` over `[l, u]` at `N` samples. -/
noncomputable def samplingError (g : ℝ → ℝ) (M l u : ℝ) (N : ℕ) : ℝ :=
  (sampleSup g l u N - sampleInf g l u N) / 2 + M * ((u - l) / N)

/-- Half the range `g` spans over the box, with no sampling in it. -/
noncomputable def boxHalfRange (g : ℝ → ℝ) (l u : ℝ) : ℝ :=
  (sSup (g '' Set.Icc l u) - sInf (g '' Set.Icc l u)) / 2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
