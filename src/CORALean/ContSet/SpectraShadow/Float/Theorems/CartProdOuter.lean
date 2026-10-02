import CORALean.ContSet.SpectraShadow.Float.Operations.CartProd
import CORALean.ContSet.SpectraShadow.Float.Theorems.PadLeftOuter
import CORALean.ContSet.SpectraShadow.Float.Theorems.PadRightOuter
import CORALean.ContSet.SpectraShadow.Float.Theorems.PlusOuter
import CORALean.Global.Block

/-!
# `SpectraShadow.cartProd` contains the Cartesian product

The product's points are the sums of the two embeddings, each inside its padded shadow, and
`plus_outer` takes the sum of the padded shadows into the result.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.cartProd_outer (S : SpectraShadow 𝕋 n) (T : SpectraShadow 𝕋 m) :
    (fun p : Vec ℝ n × Vec ℝ m => (Fin.append p.1 p.2 : Vec ℝ (n + m)))
      '' (S.construct ×ˢ T.construct) ⊆ (S.cartProd T).construct := by -- --- PROOF ---
  rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
  refine SpectraShadow.plus_outer _ _ ?_
  -- the point is the sum of its two embeddings, one in each padded shadow
  have hsum : blockPadLeft n m x + blockPadRight n m y = Fin.append x y := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [blockPadLeft, blockPadRight]
  exact ⟨_, SpectraShadow.padLeft_outer S m ⟨x, hx, rfl⟩, _,
    SpectraShadow.padRight_outer n T ⟨y, hy, rfl⟩, hsum⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
