module

public import CORALean.ContSet.Zonotope.Real.Operations.DiffusionPropStep
public import CORALean.ContSet.Zonotope.Real.Theorems.DiffusionPropLuenbergerOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.DiffusionUpdateOuter

@[expose] public section

/-!
# One instant of the set-propagation diffusion observer holds the next state

[1, Alg. 2], one instant: a state `x` in the zonotope of every node, whose output `ȳⁱ` meets every
node's strips `|Γⁱ x - ȳⁱ| ≤ rⁱ`, goes on to `F x + Q β`, `|β| ≤ 1`, in the zonotope of every node
after Steps 1-2. Step 1 keeps it (`diffusionPropLuenberger_outer`, [1, Thm. 2]) and Step 2 keeps
what every neighbour keeps (`diffusionUpdate_outer`, [1, Thm. 1]). The measurement is paired with
the state `x` the update starts from, as in Eq. 27 of [1, Thm. 2], not with the state it ends at.
The weights of Step 2 need `tr(Ḡʲ Ḡʲᵀ) > 0` for every shared zonotope, [1, Prop. 1].
## References

* [1] A. Alanwar, J. J. Rath, H. Said, K. H. Johansson and M. Althoff. "Distributed Set-Based
      Observers Using Diffusion Strategies". Journal of the Franklin Institute,
      360(10):6976-6993, 2023. arXiv:2003.10347.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nq N : ℕ} {p m : Fin N → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.diffusionPropStep_outer [∀ i, NeZero (m i)] (F : Mat ℝ n n) (Q : Mat ℝ n nq)
    (Γ : ∀ i, Mat ℝ (p i) n) (r yb : ∀ i, Vec ℝ (p i)) (nb : ∀ i, Fin (m i) → Fin N) (o : ℕ)
    (Zh : Fin N → Zonotope (Vec ℝ n)) (x : Vec ℝ n) (β : Vec ℝ nq) (hβ : ∀ j, |β j| ≤ 1)
    (hx : ∀ i, x ∈ (Zh i).construct) (hy : ∀ i j, |(Γ i *ᵥ x - yb i) j| ≤ r i j)
    (hα : ∀ i a, 0 < ∑ s, ∑ l,
      ((Zonotope.diffusionPropLuenberger F Q Γ r yb Zh (nb i a)).G l s) ^ 2) (i : Fin N) :
    F *ᵥ x + Q *ᵥ β ∈
      (Zonotope.diffusionPropStep F Q Γ r yb nb o Zh i).construct := by
  unfold Zonotope.diffusionPropStep
  exact Zonotope.diffusionUpdate_outer o _ (hα i) (Set.mem_iInter.mpr fun a =>
    Zonotope.diffusionPropLuenberger_outer F Q Γ r yb Zh x β hβ (nb i a) (hx (nb i a))
      (hy (nb i a)))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
