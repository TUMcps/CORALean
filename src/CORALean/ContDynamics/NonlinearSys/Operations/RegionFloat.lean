module

public import CORALean.ContDynamics.NonlinearSys.Definitions.FloatModel

@[expose] public section

/-!
# The box a float step stays in, checked

A step's certificate holds only where the run is, so the run has to be shown to
stay in the box `X ⊕ [-δ, δ]` the abstraction error is taken over. The check is
the one `confined_of_ball` proves sound: `M` bounds the model's `‖f‖∞` over that
box and the input box, and `MΔt < δ` means no run starting in `X` can reach its
edge within `Δt`. `ltStrict` makes the comparison strict, as the lemma needs.

`δ = (2M₀ + 1)Δt` is a guess from the bound `M₀` over `X` alone: twice what a
state moves at the speeds it starts with, plus a margin for a field that vanishes
there. A guess that fails costs the run, never its soundness.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `X ⊕ [-δ, δ]` at `δ = (2M₀ + 1)Δt`, if the field's bound `M` over it and `U`
keeps `MΔt < δ`; `none` otherwise. -/
def NonlinearSys.FloatModel.regionFloat (fm : NonlinearSys.FloatModel 𝕋 n m) (Δt : 𝕋)
    (X : Interval (Vec 𝕋 n)) (U : Interval (Vec 𝕋 m)) : Option (Interval (Vec 𝕋 n)) :=
  let bound := fun (I : Interval (Vec 𝕋 n)) =>                     -- ‖I‖∞, exactly
    maximumOver fun i => maximum (absolute (I.inf i)) (absolute (I.sup i))
  let M₀ := bound (fm.f X U)                                        -- ‖f‖∞ over X × U
  let δ := mulUp (addUp (addUp M₀ M₀) one) Δt                       -- δ = (2M₀ + 1)Δt
  let Ω : Interval (Vec 𝕋 n) := ⟨fun i => subDown (X.inf i) δ, fun i => addUp (X.sup i) δ⟩
  let M := bound (fm.f Ω U)                                         -- ‖f‖∞ over Ω × U
  let picard := fun (Ω : Interval (Vec 𝕋 n)) =>                   -- X ⊕ [0, Δt] f(Ω × U)
    let F := fm.f Ω U
    (⟨fun i => addDown (X.inf i) (minimum zero (mulDown Δt (F.inf i))),
      fun i => addUp (X.sup i) (maximum zero (mulUp Δt (F.sup i)))⟩ : Interval (Vec 𝕋 n))
  if ltStrict (mulUp M Δt) δ then some (picard (picard Ω)) else none  -- MΔt < δ, or fail

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
