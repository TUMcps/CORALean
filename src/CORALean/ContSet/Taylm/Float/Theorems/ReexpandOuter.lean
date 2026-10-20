module

public import CORALean.ContSet.Taylm.Float.Operations.Reexpand
public import CORALean.ContSet.Taylm.Float.Theorems.ReexpandAtOuter

@[expose] public section

/-!
# `Taylm.reexpand` encloses the function on the sub-box

Variable by variable, `reexpandAt_outer` carries the enclosure through each substitution
`sₖ ↦ mₖ + rₖ sₖ`; the variables are distinct, so each substitution reads the original `sₖ`, and
the whole composite is `s ↦ f (m + r ⊙ s)`. The sub-box `|mₖ| + |rₖ| ≤ 1` keeps every substituted
point in the normalized box, where the original remainder holds.

## Inputs
* `T` – Taylor model
* `f` – enclosed function
* `m` – centers
* `r` – radii

## Hypotheses
* `h` – the model encloses the function
* `hmr` – center plus radius stays within the unit interval in each coordinate

## Conclusion
* the result encloses the function on the sub-box
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The substitution at the variables of a list of distinct ones. -/
theorem Taylm.aux_reexpand_foldl (m r : Vec 𝕋 n)
    (hmr : ∀ k, |toReal (m k)| + |toReal (r k)| ≤ 1) : -- --- CONCL ---
    ∀ (l : List (Fin n)), l.Nodup → ∀ (T : Taylm 𝕋 n) (g : Vec ℝ n → ℝ), T.Encloses g →
      (l.foldl (fun T k => T.reexpandAt k (m k) (r k)) T).Encloses fun s =>
        g fun j => if j ∈ l then toReal (m j) + toReal (r j) * s j else s j := by -- --- PROOF ---
  intro l
  induction l with
  | nil => intro _ T g h; simpa using h
  | cons k l ih =>
    intro hnd T g h
    have hk : k ∉ l := (List.nodup_cons.mp hnd).1
    -- the head variable by the step theorem, the others by the induction hypothesis
    have h' := ih (List.nodup_cons.mp hnd).2 _ _ (Taylm.reexpandAt_outer h k (m k) (r k) (hmr k))
    -- the two substitutions compose to the one over the whole list, the head not being in the rest
    have hfun : (fun s : Vec ℝ n => g fun j =>
        if j ∈ k :: l then toReal (m j) + toReal (r j) * s j else s j) =
        fun s => g (Function.update (fun j => if j ∈ l then toReal (m j) + toReal (r j) * s j
          else s j) k (toReal (m k) + toReal (r k) * (if k ∈ l then toReal (m k)
            + toReal (r k) * s k else s k))) := by
      funext s
      congr 1
      funext j
      by_cases hj : j = k
      · subst hj
        simp [hk]
      · simp [hj]
    rw [List.foldl_cons, hfun]
    exact h'


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.reexpand_outer {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) (m r : Vec 𝕋 n)
    (hmr : ∀ k, |toReal (m k)| + |toReal (r k)| ≤ 1) :
    (T.reexpand m r).Encloses
      fun s => f fun k => toReal (m k) + toReal (r k) * s k := by
  -- every variable is substituted, the list of them being distinct
  have := Taylm.aux_reexpand_foldl m r hmr (List.finRange n) (List.nodup_finRange n) T f h
  simpa [Taylm.reexpand] using this

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
