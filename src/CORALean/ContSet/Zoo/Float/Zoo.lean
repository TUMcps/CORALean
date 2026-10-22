module

public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.SetIntersection.SetIntersection

@[expose] public section

/-!
# Zoos over a floating-point scalar: the representation

CORA's `zoo` with its two members over `𝕋`: an optional Taylor model (`taylm(int)`) and an
optional interval, as in the exact layer's `Zoo`. A member encloses the function on the box `[-1,
1]ⁿ` through its stored floats (`nominal`): the Taylor model as `Taylm.Encloses`, the interval as
holding the function's value at every box point.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A zoo over floats: an optional Taylor model and an optional interval, each an enclosure of the
same function. -/
structure Zoo (𝕋 : Type) (n : ℕ) where
  taylm : Option (Taylm 𝕋 n)
  ivl : Option (Interval (Vec 𝕋 1))

/-- One enclosure a zoo holds, as a set of functions: the Taylor model, or the interval. -/
inductive Zoo.Member (𝕋 : Type) (n : ℕ) where
  | taylm (T : Taylm 𝕋 n)
  | ivl (I : Interval (Vec 𝕋 1))

/-- The functions on the box that a member encloses through its stored floats: for a Taylor
model its `Encloses`, for an interval those whose value at every box point it holds. -/
instance [SoundFloatArithmetic 𝕋] : ContSet (Zoo.Member 𝕋 n) (Vec ℝ n → ℝ) where
  construct
    | .taylm T => {f | T.Encloses f}
    | .ivl I => {f | ∀ t ∈ Real.Taylm.box n, (fun _ => f t : Vec ℝ 1) ∈ I.construct}

/-- The members a zoo holds, as a `SetIntersection`: an absent member is left out, which reads
it as every function. -/
def Zoo.members (Z : Zoo 𝕋 n) : SetIntersection (Zoo.Member 𝕋 n) :=
  ⟨Z.taylm.toList.map .taylm ++ Z.ivl.toList.map .ivl⟩

/-- A zoo denotes the functions all its members enclose: CORA's intersection of enclosures. -/
instance [SoundFloatArithmetic 𝕋] : ContSet (Zoo 𝕋 n) (Vec ℝ n → ℝ) :=
  ⟨fun Z => ContSet.construct Z.members⟩

/-- Every member encloses `f` on the box. -/
def Zoo.Encloses [SoundFloatArithmetic 𝕋] (Z : Zoo 𝕋 n) (f : Vec ℝ n → ℝ) : Prop := f ∈ Z

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
