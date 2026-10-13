import CORALean.Global.RobustUnderApproxBox

/-!
# The product of the mean-value AE extensions of the components is inside the range

[1, Thm. 3]: for `f : ℝᵐ → ℝⁿ` and `π : {1, …, m} → {1, …, n}`, the product `z` of the
mean-value AE extensions (5) of [1, Thm. 2] of the components, component `i` having the
inputs `π⁻¹(i)` existential and the others universal, is inside `range(f, x)`.

The extension of component `i` is the inner interval of `Thm. 2`, so the hypotheses are
`Thm. 2`'s for each component: `f₀ᵢ ∋ fᵢ(c(x))`, `|∂ⱼfᵢ| ≥ ∇̲ᵢⱼ` on the box for the inputs
`j ∈ π⁻¹(i)`, and `|∂ⱼfᵢ| ≤ ∇̄ᵢⱼ` for the other inputs at the points whose `π⁻¹(i)` inputs
are at the centre. `f` is `C¹`, the standing assumption of [1], and the box is nonempty
(`lo ≤ hi`). The proof does not go through Goldsztejn's continuous selections, see
[`RobustUnderApproxBox.lean`](RobustUnderApproxBox.lean). A `π` that is not surjective is
no case of its own: a component without existential input has `∇̲`-sum zero.

## References

* [1] E. Goubault and S. Putot. "Robust Under-Approximations and Application to
      Reachability of Non-Linear Control Systems With Disturbances". IEEE Control Systems
      Letters, 4(4):928-933, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 3]: the product of the inner intervals of `Thm. 2` of the components is inside
`range(f, x)`. -/
theorem meanValueBox_subset_image {f : (Fin m → ℝ) → Fin n → ℝ} {π : Fin m → Fin n}
    {lo hi : Fin m → ℝ} (hlh : lo ≤ hi) (hf : ∀ i, ContDiff ℝ 1 fun x => f x i)
    {f0lo f0hi : Fin n → ℝ}
    (hf0 : ∀ i, f (fun j => (lo j + hi j) / 2) i ∈ Icc (f0lo i) (f0hi i))
    (dwhi dulo : Fin n → Fin m → ℝ)
    (hw : ∀ i, ∀ y ∈ Icc lo hi, (∀ j, π j = i → y j = (lo j + hi j) / 2) →
      ∀ j, π j ≠ i → |fderiv ℝ (fun x => f x i) y (Pi.single j 1)| ≤ dwhi i j)
    (hu : ∀ i, ∀ y ∈ Icc lo hi, ∀ j, π j = i →
      dulo i j ≤ |fderiv ℝ (fun x => f x i) y (Pi.single j 1)|) :
    Icc (fun i => f0hi i - ∑ j with π j = i, dulo i j * ((hi j - lo j) / 2)
        + ∑ j with π j ≠ i, dwhi i j * ((hi j - lo j) / 2))
      (fun i => f0lo i + ∑ j with π j = i, dulo i j * ((hi j - lo j) / 2)
        - ∑ j with π j ≠ i, dwhi i j * ((hi j - lo j) / 2))
      ⊆ f '' Icc lo hi := by -- --- PROOF ---
  intro z hz
  have hc : (fun j => (lo j + hi j) / 2) ∈ Icc lo hi :=
    ⟨fun j => by linarith [hlh j], fun j => by linarith [hlh j]⟩
  obtain ⟨x, hx, -, hfx⟩ := exists_eq_of_mean_value_box (π := fun j => some (π j)) hlh hf hf0
    dwhi dulo (fun i y hy hyE j hj => hw i y hy (fun j' hj' => hyE j' (by simp [hj'])) j
      (by simpa using hj)) (fun i y hy j hj => hu i y hy j (by simpa using hj))
    (z := z) (w := fun j => (lo j + hi j) / 2) (by simpa using hz) hc
  exact ⟨x, hx, hfx⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
