import CORALean.ContSet.SpectraShadow.Float.Theorems.InfExact
import CORALean.ContSet.SpectraShadow.Float.Theorems.InterOuter
import CORALean.ContSet.Conversion.Float.Zonotope_to_SpectraShadow
import CORALean.ContSet.ZonoBundle.Float.ZonoBundle

/-!
# A zonotope bundle as a spectrahedral shadow, over a floating-point scalar

As over ℝ: every member through the float `Zonotope.spectraShadow`, the results intersected in
order by the float `SpectraShadow.inter`, an empty family (the whole space) as
`SpectraShadow.Inf`. Each member's conversion and each intersection is outer, so the result
encloses the bundle; it is not claimed to equal it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def ZonoBundle.spectraShadow (zB : ZonoBundle (Vec 𝕋 n)) : SpectraShadow 𝕋 (Vec 𝕋 n) :=
  match List.ofFn fun i => Zonotope.spectraShadow (zB.Z i) with
  | [] => SpectraShadow.Inf n                    -- no member: the whole space
  | S :: Ss => Ss.foldl SpectraShadow.inter S    -- `and_` of the members, in order


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of the start and of every shadow folded in is a point of the left fold of `inter`. -/
theorem ZonoBundle.aux_mem_foldl_inter {x : Vec ℝ n} :
    ∀ (Ss : List (SpectraShadow 𝕋 (Vec 𝕋 n))) (S : SpectraShadow 𝕋 (Vec 𝕋 n)), x ∈ S.construct →
      (∀ T ∈ Ss, x ∈ T.construct) → x ∈ (Ss.foldl SpectraShadow.inter S).construct
  | [], _, h, _ => h
  | T :: Ts, S, h, hT => ZonoBundle.aux_mem_foldl_inter Ts (S.inter T)
      (SpectraShadow.inter_outer S T ⟨h, hT T List.mem_cons_self⟩)
      fun U hU => hT U (List.mem_cons_of_mem T hU)


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.spectraShadow_contains (zB : ZonoBundle (Vec 𝕋 n)) :
    zB.construct ⊆ zB.spectraShadow.construct := by -- --- PROOF ---
  intro x hx
  -- every member's shadow holds the point
  have hall : ∀ T ∈ List.ofFn (fun i => Zonotope.spectraShadow (zB.Z i)), x ∈ T.construct := by
    intro T hT
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hT
    exact Zonotope.spectraShadow_contains _ (Set.mem_iInter.mp hx i)
  unfold ZonoBundle.spectraShadow
  -- so the fold of their intersections does, or the whole space when there is none
  split
  · rw [SpectraShadow.Inf_exact]
    exact Set.mem_univ x
  · rename_i S Ss hL
    rw [hL] at hall
    exact ZonoBundle.aux_mem_foldl_inter Ss S (hall S List.mem_cons_self)
      fun T hT => hall T (List.mem_cons_of_mem S hT)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
