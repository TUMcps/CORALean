module

public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionInner
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionSet
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpIntegralSubTaylorLe
public import CORALean.ContSet.Interval.Real.Theorems.MemMat

@[expose] public section

/-!
# The inner approximation sits inside the outer one

Holding the input at one point `s` of `U` puts `inputTerm Δt i *ᵥ s` in every summand of the outer
approximation at once, and what the series has left past `η` is `expIntegral - ∑ᵢ inputTerm`, whose
`l∞` operator norm `norm_expIntegral_sub_taylor_le` bounds by `Δt·E(Δt,η)`, exactly the half-width
of `inputRemainder`, entry by entry. No convexity, closedness or boundedness of `U` is used: the two
sets are compared through one point of `U` at a time, and the enclosure the exact particular
solution needs (which does use them) is never invoked.

## Inputs
* `sys` – linear system
* `U` – input set
* `Δt` – step length
* `η` – Taylor order

## Hypotheses
* `hΔt` – step length nonnegative
* `hε` – scaled norm small enough for the Taylor order

## Conclusion
* the inner approximation lies in the outer one

## References

* [1] [M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control,
      2026.](../../../../../references/2026/wetzlinger-tac-backward-reachability.md)
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `inputTerm` is the order the integrated exponential's series has there. -/
private theorem LinearSys.aux_inputTerm_eq (sys : LinearSys 𝕋 n) (Δt : ℝ) (i : ℕ) :
    sys.inputTerm Δt i = ((Nat.factorial (i + 1) : ℝ)⁻¹ * Δt ^ (i + 1)) • toRealMat sys.A ^ i := by
  rw [LinearSys.inputTerm]
  congr 1
  field_simp

/-- One point of `U` held over every summand at once. -/
private theorem LinearSys.aux_sum_mulVec_mem (sys : LinearSys 𝕋 n) {U : S n} (Δt : ℝ)
    {s : Vec ℝ n} (hs : s ∈ construct U) (m : ℕ) : -- --- CONCL ---
    (∑ i ∈ Finset.range m, sys.inputTerm Δt i) *ᵥ s
      ∈ ∑ i ∈ Finset.range m,
        (fun v => sys.inputTerm Δt i *ᵥ v) '' construct U := by -- --- PROOF ---
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Matrix.add_mulVec]
    exact Set.add_mem_add ih (Set.mem_image_of_mem _ hs)


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1]: the two approximations are nested, the exact solution between
them. -/
theorem LinearSys.inputSolutionInner_subset_inputSolutionSet (sys : LinearSys 𝕋 n) {U : S n}
    {Δt : ℝ} (hΔt : 0 ≤ Δt) (η : ℕ)
    (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) : -- --- CONCL ---
    sys.inputSolutionInner U Δt ⊆ sys.inputSolutionSet U Δt η := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  rintro _ ⟨s, hs, rfl⟩
  set T := ∑ i ∈ Finset.range (η + 1), sys.inputTerm Δt i with hT
  -- the series past order `η`, as a matrix the remainder interval contains
  have hrem : ‖MatExp.expIntegral A Δt - T‖ ≤ Δt * MatExp.expRemainderBound (Δt • A) η := by
    have h := MatExp.norm_expIntegral_sub_taylor_le A hΔt η hε
    have hTeq : T = ∑ i ∈ Finset.range (η + 1),
        ((Nat.factorial (i + 1) : ℝ)⁻¹ * Δt ^ (i + 1)) • A ^ i :=
      Finset.sum_congr rfl fun i _ => sys.aux_inputTerm_eq Δt i
    rwa [hTeq]
  have hmem : MatExp.expIntegral A Δt - T
      ∈ (MatExp.inputRemainder A Δt η).construct := by
    refine Interval.mem_mat_iff.mpr fun i j => ?_
    have hentry := abs_entry_le_norm (MatExp.expIntegral A Δt - T) i j
    rw [MatExp.inputRemainder]
    constructor <;> [skip; skip] <;>
      [linarith [abs_le.mp (le_trans hentry hrem) |>.1];
       linarith [abs_le.mp (le_trans hentry hrem) |>.2]]
  -- the exact orders, then what is left, both at the same point of `U`
  have hsplit : MatExp.expIntegral A Δt *ᵥ s
      = T *ᵥ s + (MatExp.expIntegral A Δt - T) *ᵥ s := by
    rw [Matrix.sub_mulVec]
    abel
  show MatExp.expIntegral A Δt *ᵥ s ∈ sys.inputSolutionSet U Δt η
  rw [LinearSys.inputSolutionSet, hsplit]
  exact Set.add_mem_add (sys.aux_sum_mulVec_mem Δt hs (η + 1))
    (Set.mem_biUnion hmem (Set.mem_image_of_mem _ hs))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
