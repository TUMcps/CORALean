module

public import CORALean.ContSet.Ellipsoid.Float.Operations.ContainsPoint
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IsPsdSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.QuadLeQuadUp
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Real.Theorems.AddMulVecMemConstruct

@[expose] public section

/-!
# A `true` from `Ellipsoid.containsPoint` proves membership

The certified `Q` makes the nominal part the ellipsoid of `Q`; `wᵀ Q w ≤ quadUp w ≤ 1` puts
`q + Q w` in it (`Real.Ellipsoid.add_mulVec_mem_construct`), and the remainder `p - q - Q w` lies
between the two directed roundings the test compared with the error box, so in the box.

## Inputs
* `E` – ellipsoid
* `p` – point
* `w` – solve of `Q w = p - q`

## Hypotheses
* `h` – `containsPoint` returns `true`

## Conclusion
* `p` lies in `E`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.containsPoint_sound {E : Ellipsoid 𝕋 n} {p w : Vec 𝕋 n}
    (h : E.containsPoint p w = true) : toRealVec p ∈ E.construct := by -- --- PROOF ---
  simp only [Ellipsoid.containsPoint, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨hpsd, hw⟩, hbox⟩ := h
  have hpsd' := Ellipsoid.posSemidef_of_isPsd hpsd
  -- the nominal point `q + Q w`
  have hq : toRealVec w ⬝ᵥ (toRealMat E.Q *ᵥ toRealVec w) ≤ 1 :=
    le_trans (E.quad_le_quadUp w) ((toReal_le_of_le hw).trans_eq toReal_one)
  have hy : toRealVec E.q + toRealMat E.Q *ᵥ toRealVec w ∈ nominalSet E := by
    show _ ∈ (nominal E).ellipsoid.construct
    rw [Ellipsoid.nominal_of_psd hpsd']
    exact Real.Ellipsoid.add_mulVec_mem_construct ⟨toRealMat E.Q, toRealVec E.q, hpsd'⟩ hq
  refine ⟨_, hy, toRealVec p - (toRealVec E.q + toRealMat E.Q *ᵥ toRealVec w), fun i => ?_,
    by abel⟩
  -- the remainder lies between the two roundings the test compared with the box
  obtain ⟨hlo, hhi⟩ := hbox i
  have d₁ : (toRealMat E.Q *ᵥ toRealVec w) i ≤ toReal (mulVecUp E.Q w i) := le_dotUp (E.Q i) w
  have d₂ : toReal (mulVecDown E.Q w i) ≤ (toRealMat E.Q *ᵥ toRealVec w) i := dotDown_le (E.Q i) w
  have a₁ := add_le_addUp (E.q i) (mulVecUp E.Q w i)
  have a₂ := addDown_le_add (E.q i) (mulVecDown E.Q w i)
  have s₁ := subDown_le_sub (p i) (addUp (E.q i) (mulVecUp E.Q w i))
  have s₂ := sub_le_subUp (p i) (addDown (E.q i) (mulVecDown E.Q w i))
  have l₁ := toReal_le_of_le hlo
  have l₂ := toReal_le_of_le hhi
  show toReal (E.I_error.inf i) ≤ toReal (p i) - (toReal (E.q i) + _)
    ∧ toReal (p i) - (toReal (E.q i) + _) ≤ toReal (E.I_error.sup i)
  constructor <;> linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
