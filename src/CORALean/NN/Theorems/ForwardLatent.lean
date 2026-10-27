module

public import CORALean.NN.Definitions.IsRelaxationOf
public import CORALean.NN.Theorems.LeForwardH
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The input set and the output enclosure are shadows of one latent space

[1, Sec. 3]: propagating a zonotope `X = ⟨c_x, G_x⟩_Z` through the layers changes the projection,
not the factors. For every factor `β ∈ B_{q₀}` of a point of `X` there is a factor `β' ∈ B_{q_κ}`
of the output `Y = enclose(Φ, X)` whose first `q₀` entries are `β`, with `Φ(c_x + G_x β) =
c_y + G_y β'`, [1, Eq. 6]. A linear layer keeps the factors; an activation keeps them and appends
one for each neuron's approximation error, which needs the errors to bound `ϕ - m x` pointwise
(`SetBasedNet.IsRelaxationOf`), not only the set-level enclosure of [1, Prop. 1].

## Inputs
* `N` – set-based network
* `Φ` – the function it encloses
* `X` – input zonotope
* `β` – factor of a point of `X`

## Hypotheses
* `hN` – `N` relaxes `Φ` with pointwise approximation errors
* `hβ` – `β` lies in the unit box

## Conclusion
* a factor of the output, extending `β`, reaches `Φ` of the point

## References

* [1] [L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for Neural
      Network Verification". International Conference on Learning Representations,
      2026.](../../../../references/2026/koller-iclr-latent-space.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- An approximation error inside `[e, ē]` is `½(e + ē) + γ ½(ē - e)` for some `|γ| ≤ 1`. -/
private theorem aux_exists_mid_rad {eLo eUp v : ℝ} (hlo : eLo ≤ v)
    (hup : v ≤ eUp) : -- --- CONCL ---
    ∃ γ : ℝ, |γ| ≤ 1 ∧ v = (eLo + eUp) / 2 + γ * ((eUp - eLo) / 2) := by -- --- PROOF ---
  rcases eq_or_lt_of_le (hlo.trans hup) with heq | hlt
  · exact ⟨0, by simp, by subst heq; linarith⟩
  · refine ⟨(v - (eLo + eUp) / 2) / ((eUp - eLo) / 2), ?_, ?_⟩
    · have hr : 0 < (eUp - eLo) / 2 := by linarith
      rw [abs_div, abs_of_pos hr, div_le_one hr, abs_le]
      constructor <;> linarith
    · field_simp
      ring

/-- A coordinate of a point of `X` is a point of the row `X(i)`. -/
private theorem aux_mem_row (X : Zonotope (Vec ℝ n)) (β : Fin X.h → ℝ) (hβ : ∀ j, |β j| ≤ 1)
    (i : Fin n) : (fun _ => (X.c + ∑ j, β j • X.G j) i) ∈ (X.row i).construct :=
  ⟨β, hβ, by funext; simp [Zonotope.row, Finset.sum_apply]; rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 3]: every factor of a point of `X` extends to a factor of `Y` reaching its image. -/
theorem SetBasedNet.forward_latent {N : SetBasedNet n k} {Φ : Vec ℝ n → Vec ℝ k}
    (hN : N.IsRelaxationOf Φ) (X : Zonotope (Vec ℝ n)) (β : Fin X.h → ℝ)
    (hβ : ∀ j, |β j| ≤ 1) : -- --- CONCL ---
    ∃ β' : Fin (N.forward X).h → ℝ, (∀ j, |β' j| ≤ 1) ∧
      (∀ j, β' (Fin.castLE (N.le_forward_h X) j) = β j) ∧
      Φ (X.c + ∑ j, β j • X.G j) =
        (N.forward X).c + ∑ j, β' j • (N.forward X).G j := by -- --- PROOF ---
  induction hN with
  | output => exact ⟨β, hβ, fun _ => rfl, rfl⟩
  | @linear n m k W b tail Φ _ ih =>
    -- a linear layer maps the point and its generators alike: the factors stay
    obtain ⟨β', hβ', hfirst, heq⟩ := ih (X.affine W b) β hβ
    refine ⟨β', hβ', hfirst, ?_⟩
    have hmap : W *ᵥ (X.c + ∑ j, β j • X.G j) + b = (X.affine W b).c +
        ∑ j, β j • (X.affine W b).G j := by
      simp only [Zonotope.affine, mulVec_add, mulVec_sum, mulVec_smul]
      abel
    show Φ (W *ᵥ (X.c + ∑ j, β j • X.G j) + b) = (tail.forward (X.affine W b)).c +
      ∑ j, β' j • (tail.forward (X.affine W b)).G j
    rw [hmap]
    exact heq
  | @nonlinear n k ϕ m eLo eUp tail Φ hϕ _ ih =>
    -- each neuron's error is a new factor `γ i` beside the input's own
    set x := X.c + ∑ j, β j • X.G j with hx
    have hγ : ∀ i : Fin n, ∃ γ : ℝ, |γ| ≤ 1 ∧ ϕ (x i) - m (X.row i) * x i =
        (eLo (X.row i) + eUp (X.row i)) / 2 + γ * ((eUp (X.row i) - eLo (X.row i)) / 2) :=
      fun i => aux_exists_mid_rad (hϕ _ _ (aux_mem_row X β hβ i)).1
        (hϕ _ _ (aux_mem_row X β hβ i)).2
    choose γ hγ1 hγ2 using hγ
    obtain ⟨β', hβ', hfirst, heq⟩ :=
      ih (X.imageEnclosure m eLo eUp) (Fin.append β γ) (fun j => by
        refine Fin.addCases (fun j => ?_) (fun i => ?_) j <;> simp [hβ, hγ1])
    -- the input's factors are the first `q₀` of `β ++ γ`
    refine ⟨β', hβ', fun j => ?_, ?_⟩
    · exact (congrArg β' (Fin.ext rfl)).trans ((hfirst (Fin.castAdd n j)).trans (by simp))
    · show Φ (fun i => ϕ (x i)) = (tail.forward (X.imageEnclosure m eLo eUp)).c +
        ∑ j, β' j • (tail.forward (X.imageEnclosure m eLo eUp)).G j
      -- neuron by neuron: `ϕ(x(i)) = m x(i) + ½(e + ē) + γ(i) ½(ē - e)`
      have key : (fun i => ϕ (x i)) = (X.imageEnclosure m eLo eUp).c +
          ∑ j : Fin (X.h + n), Fin.append β γ j • (X.imageEnclosure m eLo eUp).G j := by
        rw [Fin.sum_univ_add]
        funext i
        have h2 := hγ2 i
        simp only [hx, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
        simp only [Zonotope.imageEnclosure, Fin.append_left, Fin.append_right, Pi.add_apply,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_zero,
          Finset.sum_ite_eq, Finset.mem_univ, if_true, hx]
        have hs : ∑ j, β j * (m (X.row i) * X.G j i) = m (X.row i) * ∑ j, β j * X.G j i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
        rw [hs]
        linear_combination h2
      rw [key]
      exact heq

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
