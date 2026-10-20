module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_HPolytope

@[expose] public section

/-!
# A box as halfspaces: `mem_hPolytope_iff`

## Inputs
* `I` – interval
* `x` – point

## Hypotheses
* none

## Conclusion
* membership in the polytope means each coordinate lies between the ends
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Fin.addCases` does not reduce on a variable index, so which half of the
constraint list an index falls in takes a rewrite. -/
theorem Interval.aux_hPolytope_A_castAdd (I : Interval (Vec ℝ n)) (j : Fin n) :
    (Interval.hPolytope I).A (Fin.castAdd n j) = LinearMap.proj j := by
  show Fin.append (fun j : Fin n => (LinearMap.proj j : Vec ℝ n →ₗ[ℝ] ℝ))
    (fun j : Fin n => -(LinearMap.proj j : Vec ℝ n →ₗ[ℝ] ℝ)) (Fin.castAdd n j) = _
  rw [Fin.append_left]

theorem Interval.aux_hPolytope_A_natAdd (I : Interval (Vec ℝ n)) (j : Fin n) :
    (Interval.hPolytope I).A (Fin.natAdd n j) = -LinearMap.proj j := by
  show Fin.append (fun j : Fin n => (LinearMap.proj j : Vec ℝ n →ₗ[ℝ] ℝ))
    (fun j : Fin n => -(LinearMap.proj j : Vec ℝ n →ₗ[ℝ] ℝ)) (Fin.natAdd n j) = _
  rw [Fin.append_right]

-- and the bounds, the same append read on either half
theorem Interval.aux_hPolytope_b_castAdd (I : Interval (Vec ℝ n)) (j : Fin n) :
    (Interval.hPolytope I).b (Fin.castAdd n j) = I.sup j := by
  show Fin.append I.sup (fun j => -I.inf j) (Fin.castAdd n j) = _
  rw [Fin.append_left]

theorem Interval.aux_hPolytope_b_natAdd (I : Interval (Vec ℝ n)) (j : Fin n) :
    (Interval.hPolytope I).b (Fin.natAdd n j) = -I.inf j := by
  show Fin.append I.sup (fun j => -I.inf j) (Fin.natAdd n j) = _
  rw [Fin.append_right]


-- =======================================  MAIN THEOREM  ======================================= --

-- membership is those two halves read back as the box's two bounds
theorem Interval.mem_hPolytope_iff {I : Interval (Vec ℝ n)} {x : Vec ℝ n} :
    x ∈ (Interval.hPolytope I).construct ↔ ∀ j, I.inf j ≤ x j ∧ x j ≤ I.sup j := by -- --- PROOF ---
  constructor
  · rintro ⟨hle, -⟩ j
    have hup : x j ≤ I.sup j := by
      have h := hle (Fin.castAdd n j)
      rw [Interval.aux_hPolytope_A_castAdd, Interval.aux_hPolytope_b_castAdd] at h
      exact h
    have hlo : -(x j) ≤ -I.inf j := by
      have h := hle (Fin.natAdd n j)
      rw [Interval.aux_hPolytope_A_natAdd, Interval.aux_hPolytope_b_natAdd] at h
      exact h
    exact ⟨by linarith, hup⟩
  · intro h
    refine ⟨Fin.addCases (fun j => ?_) fun j => ?_, fun i => i.elim0⟩
    · rw [Interval.aux_hPolytope_A_castAdd, Interval.aux_hPolytope_b_castAdd]
      exact (h j).2
    · rw [Interval.aux_hPolytope_A_natAdd, Interval.aux_hPolytope_b_natAdd]
      show -(x j) ≤ -I.inf j
      linarith [(h j).1]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
