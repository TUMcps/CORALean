module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_HPolytope

@[expose] public section

/-!
# A box as halfspaces

CORA's `polytope(interval)`: the `2n` constraints `xⱼ ≤ supⱼ` and `-xⱼ ≤ -infⱼ`.
Exact, and the only conversion into a halfspace description that costs nothing.

`HPolytope.unitBox` is this at `[-1, 1]ⁿ`, kept separate because a constrained
zonotope's domain names it constantly and should not carry an interval around.

## Inputs
* `I` – interval

## Hypotheses
* none

## Conclusion
* halfspace polytope equals the interval
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


/-- Membership is those two halves read back as the box's two bounds. -/
theorem Interval.aux_mem_hPolytope_iff {I : Interval (Vec ℝ n)} {x : Vec ℝ n} : -- --- CONCL ---
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


-- =======================================  MAIN THEOREM  ======================================= --

-- so the two descriptions denote the same set, with nothing given away
theorem Interval.hPolytope_exact (I : Interval (Vec ℝ n)) : -- --- CONCL ---
    (Interval.hPolytope I).construct = I.construct := by -- --- PROOF ---
  ext x
  constructor
  · intro hx i
    exact Interval.aux_mem_hPolytope_iff.mp hx i
  · intro hx
    exact Interval.aux_mem_hPolytope_iff.mpr fun i => hx i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
