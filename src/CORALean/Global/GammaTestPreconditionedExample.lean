module

public import CORALean.Global.GammaTest
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The preconditioned test holds on the rotation

[1, Example 4.2]: for `f`, `x` and `y` of the rotation example, `C = M⁻¹` gives `C f(x) = x`,
so the interval Jacobian of `C f` is the identity and `C y = [-ε, ε]²` (the paper's printed
`0.5 [-ε, ε] ± 0.5 [-ε, ε]`). The inclusion (2) for `C f = id`, `x₀ = 0` (the paper's `x̃`) and
`J = I` holds for every `0 < ε < 2`.

## Inputs
* `ε` – half width of the target box

## Hypotheses
* `hε` – the half width is below two

## Conclusion
* the inclusion test holds on the preconditioned rotation

## References

* [1] A. Goldsztejn and L. Jaulin. "Inner approximation of the range of vector-valued
      functions". Reliable Computing, 14:1-23, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Example 4.2]: (2) holds for `C f = id`, `J = I` and `C y = [-ε, ε]²`, `ε < 2`. -/
theorem gammaTest_preconditioned_example {ε : ℝ} (hε : ε < 2) :
    gammaTest (fun x : Fin 2 → ℝ => x) 0 (fun _ => -2) (fun _ => 2) 1 1 (fun _ => -ε)
      (fun _ => ε) := by -- --- PROOF ---
  intro y hy J hJ v _ i
  -- `J = I`, so the off-diagonal sum vanishes and the point is `yᵢ ∈ [-ε, ε]`
  have hJe : J = 1 := Matrix.ext fun a b => le_antisymm (hJ a b).2 (hJ a b).1
  subst hJe
  have hsum : ∑ j ∈ Finset.univ.erase i,
      (1 : Matrix (Fin 2) (Fin 2) ℝ) i j * v j = 0 :=
    Finset.sum_eq_zero fun j hj => by
      simp [Matrix.one_apply_ne (Finset.ne_of_mem_erase hj).symm]
  simp only [Pi.zero_apply, sub_zero, zero_add, hsum, Matrix.one_apply_eq, div_one]
  exact ⟨by linarith [hy.1 i], by linarith [hy.2 i]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
