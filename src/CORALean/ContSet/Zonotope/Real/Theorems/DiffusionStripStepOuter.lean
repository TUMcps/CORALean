module

public import CORALean.ContSet.Zonotope.Real.Operations.DiffusionStripStep
public import CORALean.ContSet.Zonotope.Real.Theorems.DiffusionTimeUpdateOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.DiffusionUpdateOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.IntersectStripOuter

@[expose] public section

/-!
# One instant of the strip-based diffusion observer holds the next state

[1, Alg. 1], one instant: a state `x` in the predicted zonotope of every node, whose outputs meet
every node's strips `|Γⁱ x - ȳⁱ| ≤ rⁱ`, goes on to `F x + Q β`, `|β| ≤ 1`, in the predicted zonotope
of every node after Steps 1-3. Step 1 keeps `x` (`intersectStrip_outer`, [1, Lemma 1]), Step 2 keeps
what every neighbour keeps (`diffusionUpdate_outer`, [1, Thm. 1]) and Step 3 propagates it
(`diffusionTimeUpdate_outer`). The weights of Step 2 need `tr(Ḡʲ Ḡʲᵀ) > 0` for every shared
zonotope, [1, Prop. 1].

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

theorem Zonotope.diffusionStripStep_outer [∀ i, NeZero (m i)] (F : Mat ℝ n n) (Q : Mat ℝ n nq)
    (Γ : ∀ i, Mat ℝ (p i) n) (r yb : ∀ i, Vec ℝ (p i)) (nb : ∀ i, Fin (m i) → Fin N) (o : ℕ)
    (Zh : Fin N → Zonotope (Vec ℝ n)) (x : Vec ℝ n) (β : Vec ℝ nq) (hβ : ∀ j, |β j| ≤ 1)
    (hx : ∀ i, x ∈ (Zh i).construct) (hy : ∀ i j, |(Γ i *ᵥ x - yb i) j| ≤ r i j)
    (hα : ∀ i a, 0 < ∑ s, ∑ l,
      ((Zonotope.diffusionStripMeasurement Γ r yb Zh (nb i a)).G l s) ^ 2) (i : Fin N) :
    F *ᵥ x + Q *ᵥ β ∈
      (Zonotope.diffusionStripStep F Q Γ r yb nb o Zh i).construct := by -- --- PROOF ---
  unfold Zonotope.diffusionStripStep
  refine Zonotope.diffusionTimeUpdate_outer F Q _ x ?_ β hβ
  refine Zonotope.diffusionUpdate_outer o _ (hα i) (Set.mem_iInter.mpr fun a => ?_)
  -- Step 1 at the neighbour: `x` meets the strips and is in the predicted zonotope
  unfold Zonotope.diffusionStripMeasurement
  exact Zonotope.intersectStrip_outer _ _ _ _ _ ⟨hx (nb i a), hy (nb i a)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
