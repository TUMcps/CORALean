module

public import CORALean.ContSet.StarSet.Real.Operations.OfPred

@[expose] public section

/-!
# A predicate as a star set denotes what it denotes

With the identity basis and center `0`, `c + G α` is `α`, so the points are the coefficients the
predicate holds of.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet


-- =======================================  MAIN THEOREM  ======================================= --

/-- `ofPred D p` denotes the set `p` denotes in the box `D`. -/
theorem StarSet.ofPred_exact {P : ℕ → Type} [∀ m, ContSet (P m) (Vec ℝ m)] {n : ℕ}
    (D : Interval (Vec ℝ n)) (p : P n) :
    (StarSet.ofPred D p).construct = D.construct ∩ ContSet.construct p := by -- --- PROOF ---
  -- the point of the identity basis at `α` is `α`
  have hpt : ∀ (α : Fin n → ℝ) (i : Fin n),
      (0 : Vec ℝ n) i + ∑ k, (if i = k then (1 : ℝ) else 0) * α k = α i := fun α i => by
    simp
  ext x
  constructor
  · rintro ⟨α, hα, hx⟩
    have : x = α := funext fun i => (hx i).trans (hpt α i)
    exact this ▸ hα
  · intro hx
    exact ⟨x, hx, fun i => (hpt x i).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
