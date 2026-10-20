module

public import CORALean.ContSet.Zonotope.Real.Operations.QuadMapMatZono
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# With a factor per coordinate, [1, Thm. 1]'s enclosure fails

[1, Thm. 1] states its set as `{λ | λᵢ = xᵀQ⁽ⁱ⁾x, x ∈ Z, Q⁽ⁱ⁾ ∈ Q⁽ⁱ⁾}`, each `Q⁽ⁱ⁾` its own
matrix zonotope and so free of the others, while its proof, eq. (12), writes one factor
`βⱼ` for all `i`. Read as printed, the claim is false: at `n = ν = 1`, `m = 2`, `Z = {1}`,
`D⁽ⁱ⁾ = 0` and `K⁽ⁱ'¹⁾ = 1`, the coordinates may take `β = 1` and `β = -1` apart, reaching
`λ = (1, -1)`, while the enclosure is `[-1, 1] ⊗ {(1, 1)}`, the segment from `(-1, -1)` to
`(1, 1)`. `quadMapMatZono_outer` is the statement that holds, factors shared.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the printed per-coordinate version does not enclose

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1] as printed, a factor per coordinate, is not enclosed. -/
theorem Zonotope.quadMapMatZono_not_outer : -- --- CONCL ---
    ∃ (D : Fin 2 → Mat ℝ 1 1) (K : Fin 1 → Fin 2 → Mat ℝ 1 1) (Z : Zonotope (Vec ℝ 1)),
      ¬ {l : Vec ℝ 2 | ∃ x ∈ Z.construct, ∃ β : Fin 2 → Fin 1 → ℝ, (∀ i j, |β i j| ≤ 1) ∧
          ∀ i, l i = x ⬝ᵥ ((D i + ∑ j, β i j • K j i) *ᵥ x)}
        ⊆ (Z.quadMapMatZono D K).construct := by -- --- PROOF ---
  refine ⟨0, fun _ _ => 1, ⟨0, fun _ => 1, Fin.elim0⟩, fun hsub => ?_⟩
  set Zr := Zonotope.quadMapMatZono 0 (fun _ _ => (1 : Mat ℝ 1 1)) ⟨0, fun _ => 1, Fin.elim0⟩
  -- `(1, -1)`, coordinate `0` at `β = 1` and coordinate `1` at `β = -1`
  have hmem := hsub (a := ![1, -1]) ⟨fun _ => 1, ⟨Fin.elim0, fun j => j.elim0, by simp⟩,
    fun i _ => if i = 0 then 1 else -1, fun i _ => by dsimp only; split_ifs <;> simp, fun i => by
      fin_cases i <;> simp [Matrix.mulVec, dotProduct]⟩
  obtain ⟨γ, -, hγ⟩ := hmem
  -- the enclosure's one generator is `(1, 1)` and its center the origin
  have hh : Zr.h = 1 := rfl
  have : Subsingleton (Fin Zr.h) := by rw [hh]; infer_instance
  let j0 : Fin Zr.h := ⟨0, by rw [hh]; exact Nat.one_pos⟩
  have hG : ∀ i, Zr.G j0 i = 1 := fun i => by
    change (Zonotope.quadMap (fun _ => (1 : Mat ℝ 1 1)) ⟨0, fun _ => 1, Fin.elim0⟩).c i = 1
    simp [Zonotope.quadMap, Matrix.mulVec, dotProduct]
  have hc : ∀ i, Zr.c i = 0 := fun i => by
    simp [Zr, Zonotope.quadMapMatZono, Zonotope.quadMap, Matrix.mulVec, dotProduct]
  rw [Fintype.sum_subsingleton _ j0] at hγ
  have h0 := congrFun hγ 0
  have h1 := congrFun hγ 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hG, hc] at h0 h1
  norm_num at h0 h1
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
