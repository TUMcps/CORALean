module

public import CORALean.ContSet.Zonotope.Float.Definitions.Tracks
public import CORALean.ContSet.Zonotope.Float.Operations.CompactZerosFrom

@[expose] public section

/-!
# Dropping the zero generators behind the first ones keeps a tracking

`compactZerosFrom` at the generator count of `X` keeps the first generators of the image in
place and drops only certified zeros, which add nothing to a point: the weights of the kept ones
are those of the original, and the first `X.h` of them are still the weights of `X`. The kept
indices, the smallest first, begin `0, 1, …`, which is what the leading columns being kept says.

## Inputs
* `X` – zonotope
* `Y` – image of the zonotope
* `f` – map

## Hypotheses
* `h` – the image tracks the map over the zonotope

## Conclusion
* the image without its zero generators past those of `X` still tracks the map
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.compactZerosFrom_tracks {X : Zonotope (Vec 𝕋 n)} {Y : Zonotope (Vec 𝕋 m)}
    {f : Vec ℝ n → Vec ℝ m} (h : X.Tracks Y f) : -- --- CONCL ---
    X.Tracks (Y.compactZerosFrom X.h) f := by -- --- PROOF ---
  obtain ⟨hle, H⟩ := h
  set K := Finset.univ.filter fun j => Y.step_keepColumnFrom X.h j = true with hK
  set e := K.orderEmbOfFin rfl with he
  have hmem : ∀ j : Fin Y.h, j.val < X.h → j ∈ K := by
    intro j hj; simp [hK, Zonotope.step_keepColumnFrom, hj, Nat.blt_eq]
  -- a dropped column is certified zero, so it is zero as reals
  have hzero : ∀ j : Fin Y.h, j ∉ K → ∀ i, toReal (Y.G j i) = 0 := by
    intro j hj i
    have hf : Y.step_keepColumnFrom X.h j = false := by simpa [hK] using hj
    simp only [Zonotope.step_keepColumnFrom, Bool.or_eq_false_iff, Bool.not_eq_false',
      List.all_eq_true, List.mem_finRange, Bool.and_eq_true, forall_const] at hf
    have h₁ := toReal_le_of_le (hf.2 i).1
    have h₂ := toReal_le_of_le (hf.2 i).2
    rw [toReal_zero] at h₁ h₂
    exact le_antisymm h₁ h₂
  -- the first generators survive in place: the `t`-th smallest kept index is `t`
  have hpre : ∀ t : ℕ, ∀ k : Fin K.card, k.val = t → t < X.h → (e k).val = t := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro k hk hlt
      -- the index is at least `t`, the one before it being `t - 1`
      have hge : t ≤ (e k).val := by
        rcases Nat.eq_zero_or_pos t with h0 | hpos
        · omega
        · have hk0 : t - 1 < K.card := by omega
          have hlt0 : (⟨t - 1, hk0⟩ : Fin K.card) < k := by rw [Fin.lt_def]; simp only; omega
          have h1 := Fin.lt_def.mp (e.strictMono hlt0)
          have h2 := ih (t - 1) (by omega) ⟨t - 1, hk0⟩ rfl (by omega)
          omega
      -- and at most `t`, as `t` itself is kept and sits at a position before `k`
      have hle2 : (e k).val ≤ t := by
        obtain ⟨m, hm⟩ : (⟨t, by omega⟩ : Fin Y.h) ∈ Set.range e := by
          rw [he, Finset.range_orderEmbOfFin]
          exact hmem _ hlt
        by_contra hgt
        have hmk : m < k := e.lt_iff_lt.mp (Fin.lt_def.mpr (by rw [hm]; simp only; omega))
        have h3 := Fin.lt_def.mp hmk
        have h4 := ih m.val (by omega) m rfl (by omega)
        rw [hm] at h4
        simp only at h4
        omega
      omega
  have hle' : X.h ≤ K.card := by
    have := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin X.h))) (t := K)
      (fun j => Fin.castLE hle j) (fun j _ => hmem _ j.isLt)
      (fun a _ b _ hab => Fin.castLE_injective hle hab)
    simpa using this
  refine ⟨hle', fun β x hx => ?_⟩
  obtain ⟨γ, hγ, hy⟩ := H β x hx
  refine ⟨fun k => γ (e k), fun j => ?_, ?_⟩
  · -- the first kept indices are the first indices
    have hj : e (Fin.castLE hle' j) = Fin.castLE hle j := Fin.ext (hpre j.val _ rfl j.isLt)
    show γ (e (Fin.castLE hle' j)) = β j
    rw [hj]
    exact hγ j
  · obtain ⟨hγ1, eY, heY, hxy⟩ := hy
    refine ⟨fun k => hγ1 (e k), eY, heY, fun i => ?_⟩
    rw [hxy i]
    -- the dropped generators are zero, so the sums agree
    have hsum : ∑ k : Fin K.card, toReal (Y.G (e k) i) * γ (e k)
        = ∑ j, toReal (Y.G j i) * γ j := by
      refine Fintype.sum_of_injective e e.injective _ _ (fun j hj => ?_) fun _ => rfl
      have hjK : j ∉ K := by
        intro hjK
        apply hj
        rw [he, Finset.range_orderEmbOfFin K rfl]
        exact hjK
      rw [hzero j hjK i, zero_mul]
    show _ = toReal (Y.c i) + ∑ k : Fin K.card, toReal (Y.G (e k) i) * γ (e k) + eY i
    rw [hsum]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
