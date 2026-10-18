module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import CORALean.Global.Tensor

@[expose] public section

/-!
# The reach set of a set over `[kr, (k+1)r]` is `e^{Akr}` times that over `[0, r]`

`[1, Eq. 6]`'s propagation `R̂([kr, (k+1)r]) = e^{Akr} R̂([0, r])`, exactly, for the input-free
system.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reach set over `[kr, (k+1)r]` is `e^{Akr}` times the one over `[0, r]`. -/
theorem MatExp.iUnion_image_Icc_eq_image (A : Mat ℝ n n) (r : ℝ) (k : ℕ)
    (Z : Set (Vec ℝ n)) : -- --- STMT ---
    (⋃ t ∈ Set.Icc ((k : ℝ) * r) (((k : ℝ) + 1) * r), (fun x => exp (t • A) *ᵥ x) '' Z)
      = (fun y => exp (((k : ℝ) * r) • A) *ᵥ y) ''
        (⋃ t ∈ Set.Icc (0 : ℝ) r, (fun x => exp (t • A) *ᵥ x) '' Z) := by -- --- PROOF ---
  have hcomm : ∀ a b : ℝ, exp ((a + b) • A) = exp (a • A) * exp (b • A) := fun a b => by
    rw [add_smul]
    exact exp_add_of_commute (((Commute.refl A).smul_left a).smul_right b)
  ext y
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_Icc, exists_prop]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, x, hx, rfl⟩
    refine ⟨exp ((t - k * r) • A) *ᵥ x, ⟨t - k * r, ⟨by linarith, by linarith⟩, x, hx, rfl⟩, ?_⟩
    rw [mulVec_mulVec, ← hcomm]
    congr 3
    ring
  · rintro ⟨_, ⟨s, ⟨h1, h2⟩, x, hx, rfl⟩, rfl⟩
    refine ⟨k * r + s, ⟨by linarith, by linarith⟩, x, hx, ?_⟩
    rw [mulVec_mulVec, ← hcomm]


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
