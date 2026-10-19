module

public import CORALean.ContSet.Zonotope.Real.Theorems.HausdorffDistLeOfReduceCert

@[expose] public section

/-!
# Inner order reduction with a certified Hausdorff bound

`[1, Cor. 6]`: a reduced zonotope `⟨x̄, X_red⟩` with `X_red = X Γ₀`, `X = X_red Γ₁ + Δ`,
`‖[Γ₀, Γ₁]‖∞ ≤ 1` and `‖Δ‖∞ ≤ δ` (`[1, Cor. 6, Eq. 43]`) lies in `⟨x̄, X⟩` and is within `δ` of it.
`[1, Prop. 6]` with the two zonotopes' roles exchanged. The statement's "`G ∈ ℝ^{n × nₓ}`"
is the generator matrix `X`.

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.hausdorffDist_le_of_reduce_inner_cert (Z Zr : Zonotope (Vec ℝ n))
    (hc : Zr.c = Z.c) (Γ₀ : Mat ℝ Z.h Zr.h) (Γ₁ : Mat ℝ Zr.h Z.h) (Δ : Fin Z.h → Vec ℝ n)
    (δ : ℝ) (hδ : 0 ≤ δ) (h₀ : ∀ k, Zr.G k = ∑ j, Γ₀ j k • Z.G j)
    (h₁ : ∀ j, Z.G j = ∑ k, Γ₁ k j • Zr.G k + Δ j) (hn₀ : ∀ j, ∑ k, |Γ₀ j k| ≤ 1)
    (hn₁ : ∀ k, ∑ j, |Γ₁ k j| ≤ 1) (hΔ : ∀ i, ∑ j, |Δ j i| ≤ δ) : -- --- CONCL ---
    Zr.construct ⊆ Z.construct
      ∧ Metric.hausdorffDist Z.construct Zr.construct ≤ δ := by -- --- PROOF ---
  obtain ⟨hsub, hd⟩ := Zonotope.hausdorffDist_le_of_reduce_cert Zr Z hc.symm Γ₀ Γ₁ Δ δ hδ h₀ h₁
    hn₀ hn₁ hΔ
  exact ⟨hsub, by rwa [Metric.hausdorffDist_comm]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
