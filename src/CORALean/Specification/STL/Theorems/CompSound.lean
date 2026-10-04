import CORALean.Specification.STL.Operations.CompEval
import CORALean.Specification.STL.Theorems.SatAnd
import CORALean.Specification.STL.Theorems.SatNext

/-!
# Rewriting the parts of a composition is sound

[1, Lemma 3]: if `ξ ⊨ₜ φᵢ ⇐ ξ ⊨ₜ φ'ᵢ` for all `i` and `ξ`, then `M ⊨ₜ f(φ) ⇐ M ⊨ₜ f(φ')`, for `M =
C(R)` and any other set of traces; the paper's induction over `∧`, `∨` and `X_c`.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem STL.Comp.aux_sat_eval_of {n : ℕ} {φ φ' : Fin n → STL.Formula X}
    (h : ∀ i ξ, (φ' i).Sat ξ → (φ i).Sat ξ) (f : STL.Comp n) (ξ : ℝ≥0 → X)
    (hf : (f.eval φ').Sat ξ) : (f.eval φ).Sat ξ := by -- --- PROOF ---
  induction f generalizing ξ with
  | hole i => exact h i ξ hf
  | and f g ihf ihg =>
    rw [STL.Comp.eval, STL.Formula.sat_and] at hf
    rw [STL.Comp.eval, STL.Formula.sat_and]
    exact ⟨ihf ξ hf.1, ihg ξ hf.2⟩
  | or f g ihf ihg => exact (hf : _ ∨ _).imp (ihf ξ) (ihg ξ)
  | next c f ih =>
    -- the next-operator shifts the trace, which is why `ξ` is generalised
    rw [STL.Comp.eval, STL.Formula.sat_next] at hf
    rw [STL.Comp.eval, STL.Formula.sat_next]
    exact ih _ hf


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Comp.holdsOn_eval_of {n : ℕ} {φ φ' : Fin n → STL.Formula X}
    (h : ∀ i ξ, (φ' i).Sat ξ → (φ i).Sat ξ) (f : STL.Comp n) {M : Set (ℝ≥0 → X)}
    (hM : (f.eval φ').HoldsOn M) : (f.eval φ).HoldsOn M :=
  fun ξ hξ => STL.Comp.aux_sat_eval_of h f ξ (hM ξ hξ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
