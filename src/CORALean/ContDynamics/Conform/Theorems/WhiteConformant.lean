import CORALean.ContDynamics.Conform.Theorems.MemGloSetIffGen

/-!
# [1, Thm. 2]: a feasible point of the white-box program is reachset conformant

[1, Alg. 1] builds the program and hands it to a solver; what is proved here is what
every point it may return guarantees.

Any `(α, c_Δ, β)` meeting (22b) in [1, Lemma 4]'s form and `α ≥ 0` (22c) puts
every measurement `y⁽ᵐ'ˢ⁾ₖ` into `Ȳₖ⁽ᵐ⁾`, hence into `Ŷₖ⁽ᵐ⁾ = Ȳₖ⁽ᵐ⁾ ⊕ Êₖ⁽ᵐ⁾` once `0 ∈ Ê` — the
conformance constraint (4b), whose `Ŷ` encloses the reachable set by [1, Thm. 1]
(`reachSetOf_subset`). [1, Lemma 3]'s halfspace form is equivalent (`mem_gloSet_iff_hRep`),
and the program's objective is the cost (`gloCost_eq`). This is what "solved" can mean
for a program handed to `linprog`: its feasible points are conformant and its objective
is `∑ₘ ∑ₖ wₖ ‖Ȳ‖_I`. For a nonlinear model `Ê ≠ {0}` and (23b) is stricter than (4b),
so the program's optimum is that of the restriction (23), not of Problem 1.1;
for a linear model `Ê = {0}` and the two coincide. (22d), `B_c c_Δ = 0`, only
restricts the point further and plays no part here.

## References

* [1] L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE
      Transactions on Automatic Control, 71(5):3014-3029, 2026.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n p q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 2]: every measurement of a feasible point lies in `Ȳ ⊕ Ê`. -/
theorem Conform.white_conformant {M S ιx ιu : Type} [Fintype ιx] [Fintype ιu] (nk : ℕ)
    (yb : M → ℕ → Vec ℝ q) (Cb : M → ℕ → Mat ℝ q n)
    (Db : M → (k : ℕ) → Fin (k + 1) → Mat ℝ q p) (cx dx : Vec ℝ n) (Gx : ιx → Vec ℝ n)
    (αx : ιx → ℝ) (cu du : Vec ℝ p) (Gu : ιu → Vec ℝ p) (αu : ιu → ℝ) (hαx : ∀ j, 0 ≤ αx j)
    (hαu : ∀ l, 0 ≤ αu l) (y : M → S → ℕ → Vec ℝ q) (E : M → ℕ → Set (Vec ℝ q))
    (hE : ∀ m k, 0 ∈ E m k)
    (hfeas : ∀ m, ∀ k < nk, ∀ s, ∃ β : ιx ⊕ (Fin (k + 1) × ιu) → ℝ,
      (∀ j, 0 ≤ Sum.elim αx (fun r : Fin (k + 1) × ιu => αu r.2) j + β j ∧
        0 ≤ Sum.elim αx (fun r : Fin (k + 1) × ιu => αu r.2) j - β j) ∧
      y m s k - yb m k = (Cb m k *ᵥ dx + ∑ i, Db m k i *ᵥ du)
        + ∑ j, β j • Sum.elim (fun j => Cb m k *ᵥ Gx j)
            (fun r : Fin (k + 1) × ιu => Db m k r.1 *ᵥ Gu r.2) j) :
    ∀ m, ∀ k < nk, ∀ s, y m s k ∈ Conform.gloSet (yb m k) (Cb m k) (Db m k) cx
        (Conform.templateZono (cx + dx) Gx αx) cu
        (fun _ => Conform.templateZono (cu + du) Gu αu) + E m k := by -- --- PROOF ---
  intro m k hk s
  -- the measurement is in `Ȳ`, and `0 ∈ Ê` adds nothing
  have hY := (Conform.mem_gloSet_iff_gen (yb m k) (Cb m k) (Db m k) cx dx Gx αx cu du Gu αu
    hαx hαu (y m s k)).mpr (hfeas m k hk s)
  exact ⟨y m s k, hY, 0, hE m k, add_zero _⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
