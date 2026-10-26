module

public import CORALean.NN.Operations.CatTransformer

@[expose] public section

/-!
# AI2's abstract transformer is sound

[1, Thm. 1]: for every CAT function `f` and every abstract input `a`,
`T_f(γ(a)) ⊆ γ(T#_f(a))`, given that `Aff`, the meet and the join are sound. By induction on how
`f` maps a point: an affine map is `Aff`'s own inclusion; a case is the point surviving the meet
with its guard, then the case's transformer, then every join it is folded into; a composition is
the two inclusions chained. `⊥` is never reached, a point being in some case.

## Inputs
* `D` – abstract domain operations
* `m` – input width
* `n` – output width
* `f` – CAT function
* `a` – abstract input

## Hypotheses
* `hD` – the domain operations are sound

## Conclusion
* the image of the abstract input lies in the transformer's output

## References

* [1] T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2: Safety
      and Robustness Certification of Neural Networks with Abstract Interpretation". 2018 IEEE
      Symposium on Security and Privacy (SP), 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {S : ℕ → Type}
  [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every element folded into the join is inside it. -/
private theorem aux_subset_foldr_join (D : CatDomain 𝕋 S) (hD : D.IsSound)
    {n : ℕ} : -- --- CONCL ---
    ∀ {k : ℕ} (g : Fin k → S n) (b : S n) (i : Fin k),
      construct (g i)
        ⊆ construct (Fin.foldr k (fun i acc => D.join (g i) acc) b) := by -- --- PROOF ---
  intro k
  induction k with
  | zero => intro _ _ i; exact i.elim0
  | succ k ih =>
    intro g b i
    rw [Fin.foldr_succ]
    refine Fin.cases ?_ (fun j => ?_) i
    · exact fun x hx => hD.join_outer _ _ (Or.inl hx)
    · exact fun x hx => hD.join_outer _ _ (Or.inr (ih (fun j => g j.succ) b j hx))


-- =======================================  MAIN THEOREM  ======================================= --

theorem Cat.transformer_outer (D : CatDomain 𝕋 S) (hD : D.IsSound) {m n : ℕ} (f : Cat 𝕋 m n)
    (a : S m) : -- --- CONCL ---
    f.image (construct a) ⊆ construct (f.transformer D a) := by -- --- PROOF ---
  rintro y ⟨x, hx, hxy⟩
  induction hxy with
  | affine W b x => exact hD.aff_outer a W b ⟨x, hx, rfl⟩
  | cases E f i hi _ _ ih =>
    -- the point survives the meet with its own guard, then that case's join
    have hmeet := hD.meet_outer a (E i) ⟨hx, hi⟩
    exact aux_subset_foldr_join D hD _ _ i (ih _ hmeet)
  | comp f₂ f₁ z _ _ ih₁ ih₂ => exact ih₂ _ (ih₁ a hx)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
