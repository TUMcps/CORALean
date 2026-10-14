module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_HPolytope
public import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.InflatedContSet.Operations.Bound
public import CORALean.ContSet.Interval.Float.Operations.BoundDot

@[expose] public section

/-!
# A zonotope as halfspaces, over a floating-point scalar — the construction

`Zonotope.nominalBoundDot`, `Zonotope.boundDot` and `Zonotope.hPolytope` are the constructions;
`Zonotope_to_HPolytope` states and proves what they guarantee.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.nominalBoundDot (Z : Zonotope (Vec 𝕋 n)) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) :
    FloatBound 𝕋 (nominalSet Z) c :=
  FloatBound.ofSupportBound ((InflatedContSet.nominal Z).supportBound c)
    (addUp (dotUp a Z.c)
      (sumUp fun j => maximum (dotUp a fun i => Z.G j i) (neg (dotDown a fun i => Z.G j i))))
    (by
      have h₁ : c (InflatedContSet.nominal Z).c ≤ toReal (dotUp a Z.c) := by
        rw [hc]
        exact le_dotUp a Z.c
      have h₂ : ∀ j, |c ((InflatedContSet.nominal Z).G j)|
          ≤ toReal (maximum (dotUp a fun i => Z.G j i)
              (neg (dotDown a fun i => Z.G j i))) := by
        intro j
        -- the nominal generator spelt out, so both sides name the same sum
        have hval : c ((InflatedContSet.nominal Z).G j)
            = ∑ k, toReal (a k) * toReal (Z.G j k) := hc _
        rw [hval, toReal_maximum, toReal_neg]
        refine abs_le.mpr ⟨?_, ?_⟩
        · have hdown := dotDown_le a fun i => Z.G j i
          have hm := le_max_right (toReal (dotUp a fun i => Z.G j i))
            (-toReal (dotDown a fun i => Z.G j i))
          linarith
        · have hup := le_dotUp a fun i => Z.G j i
          have hm := le_max_left (toReal (dotUp a fun i => Z.G j i))
            (-toReal (dotDown a fun i => Z.G j i))
          linarith
      -- and the generators' total, summed upward once
      have h₃ : (∑ j, |c ((InflatedContSet.nominal Z).G j)|)
          ≤ toReal (sumUp fun j => maximum (dotUp a fun i => Z.G j i)
              (neg (dotDown a fun i => Z.G j i))) :=
        le_trans (Finset.sum_le_sum fun j _ => h₂ j) (sum_le_sumUp _)
      have h₄ := add_le_addUp (dotUp a Z.c)
        (sumUp fun j => maximum (dotUp a fun i => Z.G j i) (neg (dotDown a fun i => Z.G j i)))
      show c (InflatedContSet.nominal Z).c + ∑ j, |c ((InflatedContSet.nominal Z).G j)| ≤ _
      linarith)

def Zonotope.boundDot (Z : Zonotope (Vec 𝕋 n)) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) : FloatBound 𝕋 Z.construct c :=
  InflatedContSet.boundOfParts (Z.nominalBoundDot a hc) (Z.I_error.boundDot a hc)

def Zonotope.hPolytope (Z : Zonotope (Vec 𝕋 n)) (Aq : Mat 𝕋 q n) : HPolytope 𝕋 (Vec 𝕋 n) :=
  HPolytope.ofBounds Aq fun i => Z.boundDot (Aq i) fun _ => rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
