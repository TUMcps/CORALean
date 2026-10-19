module

public import CORALean.ContDynamics.NonlinearSys.Theorems.VarInputsOuter
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

/-!
# `varInputs` is not the set of `[1, Eq. 7]`

[1, Eq. 7] is the set of every value
`v∆(z∆, z, u∆)`, which the paper's operator `varInputs` is printed equal to. A Minkowski
sum lets each of the three quadratic pairings choose its own
`z` and `z∆`, where one member of `Eq. 7` uses one pair in all three, so only `⊇` holds.
One dimension is enough: `B = 0`, `D = [1]`, `Rz = R∆z = [-1, 1]` and `U∆ = {0}`. A member
of `Eq. 7` is `z·z∆ + z∆²/2`, whose least value over the square is `-1/2`, while
`varInputs` is `½([-1, 1] ⊕ [-1, 1] ⊕ [0, 1])` and holds `-1`, at `z = 1`, `z∆ = -1` in
the first pairing, `z∆ = -1`, `z = 1` in the second and `z∆ = 0` in the third.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

open Matrix Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 7] as printed: the set of values of `v∆` is `varInputs`. It is not. -/
theorem varInputs_eq_counterexample : -- --- CONCL ---
    ∃ (B : Mat ℝ 1 1) (D : Fin 1 → Mat ℝ 1 1) (Rz RzΔ : PolyZonotope (Vec ℝ 1))
      (UΔ : PolyZonotope (Vec ℝ 1)),
      {v : Vec ℝ 1 | ∃ z ∈ Rz.construct, ∃ zΔ ∈ RzΔ.construct, ∃ uΔ ∈ UΔ.construct,
        v = fun i => (B *ᵥ uΔ) i
          + (2 : ℝ)⁻¹ * ∑ j, ∑ k, D i j k * (z j * zΔ k + zΔ j * z k + zΔ j * zΔ k)}
        ≠ (varInputs B D Rz RzΔ UΔ).construct := by -- --- PROOF ---
  -- the interval `[-1, 1]` and the point `{0}`, as polynomial zonotopes
  obtain ⟨box, hbox⟩ : ∃ box : PolyZonotope (Vec ℝ 1), ∀ x, x ∈ box.construct ↔ |x 0| ≤ 1 := by
    refine ⟨⟨0, 0, 1, 0, fun i => i.elim0, fun k => k.elim0, fun _ _ => 1⟩, fun x => ?_⟩
    constructor
    · rintro ⟨a, β, ha, hβ, rfl⟩
      simpa using hβ 0
    · intro hx
      refine ⟨fun k => k.elim0, fun _ => x 0, fun k => k.elim0, fun _ => hx, ?_⟩
      funext i
      fin_cases i
      simp
  obtain ⟨U0, hU0⟩ : ∃ U0 : PolyZonotope (Vec ℝ 1), (0 : Vec ℝ 1) ∈ U0.construct :=
    ⟨⟨0, 0, 0, 0, fun i => i.elim0, fun k => k.elim0, fun j => j.elim0⟩,
      fun k => k.elim0, fun j => j.elim0, fun k => k.elim0, fun j => j.elim0, by simp⟩
  refine ⟨0, fun _ => !![1], box, box, U0, fun heq => ?_⟩
  -- `-1` is in `varInputs`: the three pairings choose `(1, -1)`, `(-1, 1)` and `0`
  have hmem : (fun _ => -1 : Vec ℝ 1) ∈ (varInputs 0 (fun _ => !![1]) box box U0).construct := by
    -- the three points of the box the pairings choose
    have h1 : (fun _ => 1 : Vec ℝ 1) ∈ box.construct := (hbox _).mpr (by simp)
    have h2 : (fun _ => -1 : Vec ℝ 1) ∈ box.construct := (hbox _).mpr (by simp)
    have h3 : (0 : Vec ℝ 1) ∈ box.construct := (hbox _).mpr (by simp)
    -- split `varInputs` into `B U∆` and the half sum, then each pairing on its own
    rw [varInputs, ← PolyZonotope.plus_exact]
    refine Set.mem_add.mpr ⟨0, ?_, fun _ => -1, ?_, by simp⟩
    · rw [← PolyZonotope.mtimes_exact]
      exact ⟨0, hU0, by simp⟩
    -- the half sum of the three pairings is `-2 / 2`
    · rw [← PolyZonotope.map_exact]
      refine ⟨fun _ => -2, ?_, ?_⟩
      -- the three pairings, each at its own points
      · rw [← PolyZonotope.plus_exact, ← PolyZonotope.plus_exact]
        refine Set.mem_add.mpr ⟨PolyZonotope.quadBilin (fun _ => !![1]) (fun _ => 1) (fun _ => -1)
          + PolyZonotope.quadBilin (fun _ => !![1]) (fun _ => -1) (fun _ => 1), ?_,
          PolyZonotope.quadBilin (fun _ => !![1]) 0 0, ?_, ?_⟩
        · refine Set.mem_add.mpr ⟨_, ?_, _, ?_, rfl⟩
          · rw [← PolyZonotope.quadMapMixed_exact]
            exact ⟨((fun _ => 1), (fun _ => -1)), ⟨h1, h2⟩, rfl⟩
          · rw [← PolyZonotope.quadMapMixed_exact]
            exact ⟨((fun _ => -1), (fun _ => 1)), ⟨h2, h1⟩, rfl⟩
        · rw [← PolyZonotope.quadMap_exact]
          exact ⟨0, h3, rfl⟩
        · funext i
          fin_cases i
          simp only [Pi.add_apply]
          simp [PolyZonotope.quadBilin, Matrix.mulVec, dotProduct]
          norm_num
      · funext i
        fin_cases i
        simp
  -- but a member of `Eq. 7` is `z z∆ + z∆²/2 ≥ -1/2`
  rw [← heq] at hmem
  obtain ⟨z, hz, zΔ, hzΔ, uΔ, huΔ, hv⟩ := hmem
  have b1 := abs_le.mp ((hbox z).mp hz)
  have b2 := abs_le.mp ((hbox zΔ).mp hzΔ)
  have h0 := congrFun hv 0
  simp at h0
  nlinarith [sq_nonneg (z 0 + zΔ 0), b1.1, b1.2, b2.1, b2.2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
