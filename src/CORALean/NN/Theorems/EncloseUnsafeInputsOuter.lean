module

public import CORALean.NN.Operations.EncloseUnsafeInputs
public import CORALean.NN.Theorems.ForwardLatent
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import CORALean.ContSet.Zonotope.Real.Theorems.NegSumAbsLeSumMul
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The constrained input set encloses every unsafe input

[1, Prop. 2]: `{x ∈ X | Φ(x) ∈ U} ⊆ X|_{C≤d} ⊆ X` for the constraints
`SetBasedNet.encloseUnsafeInputs`. An unsafe `x = c_x + G_x β` has `Φ(x) = c_y + G_y β'` with
`β'` extending `β` (`SetBasedNet.forward_latent`), so `A G_y(·,[q₀]) β ≤ b - A c_y -
A G_y(·,[q_κ]\[q₀]) β'(…) ≤ d`. The latent space needs the approximation errors pointwise
(`SetBasedNet.IsRelaxationOf`); for a `Y` that only encloses `Φ(X)` the statement fails
(`SetBasedNet.encloseUnsafeInputs_counterexample`).

## Inputs
* `N` – set-based network
* `Φ` – the function it encloses
* `X` – input zonotope
* `A` – unsafe-set matrix
* `b` – unsafe-set offset

## Hypotheses
* `hN` – `N` relaxes `Φ` with pointwise approximation errors

## Conclusion
* the unsafe inputs lie in `X|_{C≤d}`, and `X|_{C≤d} ⊆ X`

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

variable {n k p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The sum over `[q_κ]` split into the first `q₀` indices and `[q_κ]\[q₀]`. -/
private theorem aux_sum_castLE_add {q₀ q : ℕ} (hq : q₀ ≤ q) (f : Fin q → ℝ) : -- --- CONCL ---
    ∑ l, f l = ∑ j : Fin q₀, f (Fin.castLE hq j) +
      ∑ l ∈ Finset.univ.filter (fun l : Fin q => q₀ ≤ l.val), f l := by -- --- PROOF ---
  rw [← Finset.sum_filter_not_add_sum_filter Finset.univ (fun l : Fin q => q₀ ≤ l.val)]
  congr 1
  symm
  exact Finset.sum_bij' (fun j _ => Fin.castLE hq j)
    (fun l hl => ⟨l.val, not_le.mp (Finset.mem_filter.mp hl).2⟩)
    (fun j _ => by simp [Finset.mem_filter, j.isLt]) (fun _ _ => Finset.mem_univ _)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2]: `{x ∈ X | Φ(x) ∈ U} ⊆ X|_{C≤d} ⊆ X`. -/
theorem SetBasedNet.encloseUnsafeInputs_outer {N : SetBasedNet n k} {Φ : Vec ℝ n → Vec ℝ k}
    (hN : N.IsRelaxationOf Φ) (X : Zonotope (Vec ℝ n)) (A : Mat ℝ p k)
    (b : Vec ℝ p) : -- --- CONCL ---
    {x ∈ X.construct | Φ x ∈ (HPolytope.ineqs A b).construct} ⊆
        (N.encloseUnsafeInputs X A b).construct ∧
      (N.encloseUnsafeInputs X A b).construct ⊆ X.construct := by -- --- PROOF ---
  refine ⟨fun x ⟨⟨β, hβ, hx⟩, hU⟩ => ⟨β, hβ, ?_, hx⟩, fun x ⟨β, hβ, _, hx⟩ => ⟨β, hβ, hx⟩⟩
  -- the output of the unsafe input in the latent space: `Φ(x) = c_y + G_y β'`
  obtain ⟨β', hβ', hfirst, hy⟩ := N.forward_latent hN X β hβ
  change β ∈ (HPolytope.ineqs (N.unsafeInputConstraints X A b).1
    (N.unsafeInputConstraints X A b).2).construct
  rw [HPolytope.mem_ineqs_iff] at hU ⊢
  intro i
  have hUi := hU i
  rw [hx, hy, mulVec_add, mulVec_sum, Pi.add_apply, Finset.sum_apply,
    aux_sum_castLE_add (N.le_forward_h X)] at hUi
  simp only [mulVec_smul, Pi.smul_apply, smul_eq_mul, hfirst] at hUi
  -- `A G_y(·,[q₀]) β` is `C β`; the rest is at least `-|A G_y(·,[q_κ]\[q₀])| 1`
  have hrest := Zonotope.neg_sum_abs_le_sum_mul
    (Finset.univ.filter (fun j : Fin (N.forward X).h => X.h ≤ j.val)) β'
    (fun j => (A *ᵥ (N.forward X).G j) i) hβ'
  simp only [SetBasedNet.unsafeInputConstraints, mulVec, dotProduct] at hUi hrest ⊢
  have hcomm := Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => mul_comm (β j)
    (∑ l, A i l * (N.forward X).G (Fin.castLE (N.le_forward_h X) j) l)
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
