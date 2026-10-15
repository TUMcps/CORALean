module

public import CORALean.ContSet.ContSet.Operations.EnlargeScalar
public import CORALean.ContSet.ContSet.Theorems.MinusScalarOuter
public import CORALean.ContSet.ContSet.Theorems.TimesOuter

@[expose] public section

/-!
# `enlargeScalar` encloses the scaling about the center
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] [Neg 𝕋] [NegScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [OfScalarPoint 𝕋 S] [ScalarCenter 𝕋 S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point `c + f ⊙ (x - c)`, `x` in `S`, `c` the center and `f` read as reals, is in
`enlargeScalar S f`: `minusScalar_outer`, `times_outer` and `plus_outer` in turn. -/
theorem ContSet.enlargeScalar_outer (s : S n) (f : Vec 𝕋 n) :
    (fun x : Vec ℝ n => toRealVec (ScalarCenter.centerVec (𝕋 := 𝕋) s) +
        fun i => toReal (f i) * (x i - toRealVec (ScalarCenter.centerVec (𝕋 := 𝕋) s) i)) ''
      construct s ⊆ construct (ContSet.enlargeScalar s f) := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  have h1 := ContSet.minusScalar_outer s (ScalarCenter.centerVec (𝕋 := 𝕋) s) ⟨x, hx, rfl⟩
  have h2 := ContSet.times_outer f (ContSet.minusScalar s (ScalarCenter.centerVec (𝕋 := 𝕋) s))
    ⟨x - toRealVec (ScalarCenter.centerVec (𝕋 := 𝕋) s), h1, rfl⟩
  exact Plus.plus_outer _ _ ⟨_, h2, toRealVec (ScalarCenter.centerVec (𝕋 := 𝕋) s),
    OfScalarPoint.mem_ofVec _, add_comm _ _⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
