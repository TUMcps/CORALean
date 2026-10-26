module

public import CORALean.NN.Operations.EncloseUnsafeInputs
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# An output enclosure that only encloses does not transfer the unsafe set

[1, Prop. 2] for `Y = enclose(Φ, X)` that is an enclosure of `Φ(X)` and nothing more: the
activation `ϕ(t) = -t` relaxed by slope `1` and errors `[0, 0]` on `X = ⟨0, [1]⟩_Z ⊂ ℝ` gives
`Y = ⟨0, [1 0]⟩_Z`, which contains `Φ(X) = [-1, 1]`, the set-level guarantee of [1, Prop. 1]. For
`U = {y | -y ≤ -½}` the constraints are `C = [-1]`, `d = -½`, so `X|_{C≤d} = [½, 1]`, which misses
the unsafe input `x = -1` (`Φ(-1) = 1`). The output factor of `Φ(x)` is `-β`, not the input's `β`:
the errors `[0, 0]` do not bound `ϕ(t) - t = -2t`, which `SetBasedNet.IsRelaxationOf` asks for.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* an output enclosure with set-level errors misses an unsafe input

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for Neural
      Network Verification". International Conference on Learning Representations, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `ϕ(t) = -t` relaxed by slope `1` and errors `[0, 0]`. -/
private def aux_N : SetBasedNet 1 1 :=
  .nonlinear (fun _ => 1) (fun _ => 0) (fun _ => 0) .output

/-- `X = ⟨0, [1]⟩_Z = [-1, 1]`. -/
private abbrev aux_X : Zonotope (Vec ℝ 1) := ⟨1, 0, fun _ _ => 1⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2] fails for an output set that only encloses `Φ(X)`. -/
theorem SetBasedNet.encloseUnsafeInputs_counterexample : -- --- CONCL ---
    ∃ (N : SetBasedNet 1 1) (Φ : Vec ℝ 1 → Vec ℝ 1) (X : Zonotope (Vec ℝ 1)) (A : Mat ℝ 1 1)
      (b : Vec ℝ 1), Φ '' X.construct ⊆ (N.forward X).construct ∧
      ¬ {x ∈ X.construct | Φ x ∈ (HPolytope.ineqs A b).construct} ⊆
        (N.encloseUnsafeInputs X A b).construct := by -- --- PROOF ---
  refine ⟨aux_N, fun x i => -x i, aux_X, fun _ _ => -1, fun _ => -1 / 2, ?_, ?_⟩
  · -- `Φ(X) = [-1, 1] ⊆ Y`: the point `-β` is reached with the factors `(-β, 0)`
    rintro _ ⟨x, ⟨β, hβ, rfl⟩, rfl⟩
    have hβ0 : |β 0| ≤ 1 := hβ 0
    refine ⟨![-β 0, 0], fun j => ?_, ?_⟩
    · have key : ∀ j : Fin 2, |(![-β 0, 0] : Fin 2 → ℝ) j| ≤ 1 := by
        intro j
        fin_cases j <;> simp [hβ0]
      exact key j
    · funext i
      change -(((0 : Vec ℝ 1) + ∑ j : Fin 1, β j • (fun _ => (1 : ℝ))) : Vec ℝ 1) i =
        ((aux_N.forward aux_X).c + ∑ j : Fin 2,
          (![-β 0, 0] : Fin 2 → ℝ) j • (aux_N.forward aux_X).G j) i
      simp [aux_N, aux_X, SetBasedNet.forward, Zonotope.imageEnclosure, Fin.append,
        Fin.addCases]
  · -- the unsafe input `x = -1` is not in `X|_{C≤d} = [½, 1]`
    intro hsub
    have hmem := hsub (a := fun _ => -1)
      ⟨⟨fun _ => -1, fun _ => by norm_num, by funext; simp [aux_X]⟩,
        (HPolytope.mem_ineqs_iff).2 fun i => by simp [mulVec, dotProduct]; norm_num⟩
    obtain ⟨β, -, hP, hx⟩ : ∃ β : Fin 1 → ℝ, (∀ j, |β j| ≤ 1) ∧
        β ∈ (HPolytope.ineqs (aux_N.unsafeInputConstraints aux_X (fun _ _ => -1)
          (fun _ => -1 / 2)).1 (aux_N.unsafeInputConstraints aux_X (fun _ _ => -1)
          (fun _ => -1 / 2)).2).construct ∧
        (fun _ => (-1 : ℝ)) = (0 : Vec ℝ 1) + ∑ j : Fin 1, β j • (fun _ => (1 : ℝ)) := hmem
    have hβ : β 0 = -1 := by
      have := congrFun hx 0
      simp at this
      linarith
    have hC := (HPolytope.mem_ineqs_iff).1 hP 0
    simp [SetBasedNet.unsafeInputConstraints, aux_N, aux_X, SetBasedNet.forward,
      Zonotope.imageEnclosure, mulVec, dotProduct, Finset.sum_filter, hβ,
      Fin.append, Fin.addCases] at hC
    -- the error generator is zero, so `d = -½` and `C β = 1 ≤ -½` fails
    rw [Finset.sum_eq_zero fun a _ => ?_] at hC
    · norm_num at hC
    · split_ifs with h1 h2
      · subst h2
        simp at h1
      · simp
      · rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
