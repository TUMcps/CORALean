module

public import CORALean.ContSet.ProbZonotope.Real.Operations.Enclose
public import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# The mean zonotope of `enclose` contains the segments from `μ` to `e^{Ar} μ + Rtrans`

For every mean `μ` of `probZ` and `a ∈ [0, 1]`, the mean zonotope of `enclose(probZ, Ar)`
contains `a μ + (1 - a)(e^{Ar} μ + Rtrans)`: the sampled points of the set
`{a x₁ + (1 - a) x₂ | x₁ ∈ probZ, x₂ ∈ e^{Ar} probZ + Rtrans}` of CORA's header, on the means.
An over-approximation of the means, not equal to them; what it says of the covariance is
nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix
open scoped MatrixOrder Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.enclose_mean_outer (P : ProbZonotope n) (Ar : Mat ℝ n n) (m : ℝ)
    (Rtrans : Vec ℝ n) {μ : Vec ℝ n} (hμ : μ ∈ P.Z.construct) {a : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) : -- --- STMT ---
    a • μ + (1 - a) • (NormedSpace.exp Ar *ᵥ μ + Rtrans)
      ∈ (P.enclose Ar m Rtrans).Z.construct := by -- --- PROOF ---
  -- `μ` is a mean of the confidence zonotope, at the zero confidence coefficients
  have h0 : (0 : Vec ℝ n) ∈ (confidenceZonotope (CFC.sqrt P.cov) m).construct :=
    ⟨0, fun _ => by simp, by simp [confidenceZonotope]⟩
  have hμ' : μ ∈ (P.zonotope m).construct := by
    rw [ProbZonotope.zonotope, ← Zonotope.plus_exact]
    exact ⟨μ, hμ, 0, h0, add_zero μ⟩
  -- the point `Rtrans` is the zonotope with no generators
  have hpt : Rtrans ∈ (⟨0, Rtrans, Fin.elim0⟩ : Zonotope (Vec ℝ n)).construct :=
    ⟨Fin.elim0, fun i => i.elim0, by simp⟩
  have hz : (NormedSpace.exp Ar - 1) *ᵥ μ + Rtrans ∈ (Zonotope.plus
      (Zonotope.mtimes (NormedSpace.exp Ar - 1) (P.zonotope m))
      ⟨0, Rtrans, Fin.elim0⟩).construct := by
    rw [← Zonotope.plus_exact]
    exact Set.add_mem_add (by rw [← Zonotope.mtimes_exact]; exact ⟨μ, hμ', rfl⟩) hpt
  -- the segment from `0` to `Zaux` lies in `deltaZ`
  have hd := Zonotope.linComb_outer (⟨0, 0, Fin.elim0⟩ : Zonotope (Vec ℝ n)) _
    ⟨0, ⟨Fin.elim0, fun i => i.elim0, by simp⟩, _, hz, a, ha, rfl⟩
  have hsum : μ + (a • (0 : Vec ℝ n) + (1 - a) • ((NormedSpace.exp Ar - 1) *ᵥ μ + Rtrans))
      ∈ (P.enclose Ar m Rtrans).Z.construct := by
    rw [ProbZonotope.enclose]
    simp only []
    rw [← Zonotope.plus_exact]
    exact Set.add_mem_add hμ hd
  -- the point is `μ` plus a point of `deltaZ`
  have e : a • μ + (1 - a) • (NormedSpace.exp Ar *ᵥ μ + Rtrans)
      = μ + (a • (0 : Vec ℝ n) + (1 - a) • ((NormedSpace.exp Ar - 1) *ᵥ μ + Rtrans)) := by
    rw [sub_mulVec, one_mulVec, smul_zero, zero_add]
    module
  rw [e]
  exact hsum

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
