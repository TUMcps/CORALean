module

public import CORALean.ContDynamics.Conform.Definitions.Glo
public import CORALean.ContDynamics.Conform.Theorems.ImageTemplateZono
public import CORALean.ContDynamics.Conform.Theorems.SingletonAddTemplateZono
public import CORALean.ContDynamics.Conform.Theorems.SumTemplateZono
public import CORALean.ContDynamics.Conform.Theorems.TemplateZonoAdd

@[expose] public section

/-!
# [1, Lemma 1]: `Ȳ` of stretched templates is a stretched template

With the uncertainty sets [1, Eq. 3], `X₀ = ⟨c_x + c_Δ,x, G_x diag(α_x)⟩` and every
`Uᵢ = ⟨c_u + c_Δ,u, G_u diag(α_u)⟩`, `Ȳ` has center `ȳ + C̄ c_Δ,x + ∑ᵢ D̄ᵢ c_Δ,u` (16a)
and generators `[C̄ G_x, D̄₀ G_u, …, D̄ₖ G_u]` (16c) stretched by `[α_x; α_u; …; α_u]`
(16b) — the initial estimates `c_x`, `c_u` cancel against the `-c_x`, `-c_u` of (7), leaving
the shifts. An equality.

## References

* [1] L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE
      Transactions on Automatic Control, 71(5):3014-3029, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n p q k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 1]: `Ȳ` with center (16a) and generators (16b)-(16c). -/
theorem Conform.gloSet_templateZono {ιx ιu : Type} [Fintype ιx] [Fintype ιu] (yb : Vec ℝ q)
    (Cb : Mat ℝ q n) (Db : Fin (k + 1) → Mat ℝ q p) (cx dx : Vec ℝ n) (Gx : ιx → Vec ℝ n)
    (αx : ιx → ℝ) (cu du : Vec ℝ p) (Gu : ιu → Vec ℝ p) (αu : ιu → ℝ) :
    Conform.gloSet yb Cb Db cx (Conform.templateZono (cx + dx) Gx αx) cu
        (fun _ => Conform.templateZono (cu + du) Gu αu)
      = Conform.templateZono (yb + Cb *ᵥ dx + ∑ i, Db i *ᵥ du)
          (Sum.elim (fun j => Cb *ᵥ Gx j) fun r : Fin (k + 1) × ιu => Db r.1 *ᵥ Gu r.2)
          (Sum.elim αx fun r => αu r.2) := by -- --- PROOF ---
  unfold Conform.gloSet
  have hx : -cx + (cx + dx) = dx := by abel
  have hu : -cu + (cu + du) = du := by abel
  rw [Conform.singleton_add_templateZono (-cx), hx, Conform.image_templateZono]
  have hsum : ∀ i : Fin (k + 1), (fun v => Db i *ᵥ v) '' ({-cu} + Conform.templateZono (cu + du)
      Gu αu) = Conform.templateZono (Db i *ᵥ du) (fun j => Db i *ᵥ Gu j) αu := fun i => by
    rw [Conform.singleton_add_templateZono, hu, Conform.image_templateZono]
  simp only [hsum]
  rw [Conform.sum_templateZono, Conform.singleton_add_templateZono, Conform.templateZono_add]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
