module

public import CORALean.DiscrDynamics.MarkovChain.Operations.Stretch

@[expose] public section

/-!
# `stretch` of a stochastic chain

`T^factor` of a column-stochastic matrix is one, and so is the average of the products
`OT T^k` that `OT` becomes.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- Stretching a chain with column-stochastic `T` and `OT` keeps both so. -/
theorem MarkovChain.stretch_mem {ι : Type} [Fintype ι] [DecidableEq ι]
    (Obj : MarkovChain.Stacked ι) {factor : ℕ} (hf : 1 ≤ factor)
    (hT : Obj.T ∈ Matrix.colStochastic ℝ ι)
    (hOT : Obj.OT ∈ Matrix.colStochastic ℝ ι) : -- --- STMT ---
    (MarkovChain.stretch Obj factor).T ∈ Matrix.colStochastic ℝ ι ∧
    (MarkovChain.stretch Obj factor).OT ∈ Matrix.colStochastic ℝ ι := by -- --- PROOF ---
  refine ⟨(Matrix.colStochastic ℝ ι).pow_mem hT factor, ?_⟩
  have hfpos : (0 : ℝ) < factor := by exact_mod_cast hf
  -- `OT` is a convex combination of the stochastic matrices `OT T^k`
  have : (MarkovChain.stretch Obj factor).OT =
      ∑ k ∈ Finset.range factor, (1 / (factor : ℝ)) • (Obj.OT * Obj.T ^ k) := by
    simp only [MarkovChain.stretch, Finset.mul_sum, Finset.smul_sum]
  rw [this]
  refine (Matrix.convex_colStochastic (R := ℝ) (n := ι)).sum_mem (t := Finset.range factor)
    (w := fun _ => 1 / (factor : ℝ)) (z := fun k => Obj.OT * Obj.T ^ k)
    (fun _ _ => by positivity) ?_ ?_
  · simp; field_simp
  · intro k _
    exact (Matrix.colStochastic ℝ ι).mul_mem hOT ((Matrix.colStochastic ℝ ι).pow_mem hT k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
