module

public import CORALean.Specification.FourValuedSignal.Definitions.Refines
public import CORALean.Specification.FourValuedSignal.Theorems.UntilSpec
public import CORALean.Specification.FourValuedSignal.Theorems.ToKleeneSignalAt
public import CORALean.Specification.FourValuedSignal.Theorems.ToKleeneSignalSpec
public import CORALean.Specification.Kleene.Theorems.Basic
public import CORALean.Specification.KleeneSignal.Theorems.UntilSpec
public import CORALean.Specification.KleeneSignal.Theorems.UntilMono
public import CORALean.Specification.STLInterval.Theorems.ZeroLeOfMemSet
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The until of four-valued signals respects refinement, and reads only the future

For valid signals the until `lhs U_I rhs` exists, and two facts make the incremental analyzer of
[1, Alg. 2] work. Refining both operands refines the result: it is the join of the Kleene untils of
the floors and of the ceilings, which `KleeneSignal.until_mono` ([1, Lemma 3]) orders. And its value
at `t` depends on the operands at the times from `t` on only, `t' - t ∈ I` having `t' ≥ t`.

## Inputs
* `l` – left operand that knows less
* `r` – right operand that knows less
* `l'` – left operand that knows more
* `r'` – right operand that knows more
* `U` – time interval

## Hypotheses
* `hl` – `l` is valid
* `hr` – `r` is valid
* `hl'` – `l'` is valid
* `hr'` – `r'` is valid

## Conclusion
* both untils exist and are valid, refining the operands refines the until, and operands that
  agree from `t` on give untils that agree at `t`

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Kleene values that agree on `True` and on `False` are equal. -/
private theorem aux_kleene_eq_of_iff (x y : Kleene) (h1 : x = .tt ↔ y = .tt)
    (h2 : x = .ff ↔ y = .ff) :
    x = y := by
  cases x <;> cases y <;> simp_all


/-- A refined value has a larger floor and a smaller ceiling. -/
private theorem aux_floor_ceil_of_refines (v w : FourValued) (h : v ≠ .ii → w = v) :
    v.floor ≤ w.floor ∧ w.ceil ≤ v.ceil := by
  cases v <;> cases w <;>
    simp_all [FourValued.floor, FourValued.ceil, Kleene.le_iff_code, Kleene.code]

/-- The floor is below the ceiling. -/
private theorem aux_floor_le_ceil (v : FourValued) : v.floor ≤ v.ceil := by
  cases v <;> simp [FourValued.floor, FourValued.ceil, Kleene.le_iff_code, Kleene.code]


/-- The four-valued until at `t` is the join of the untils of the two refinements. -/
private theorem aux_until_at_eq_join (l r s : FourValuedSignal ℝ) (hl : l.IsValid)
    (hr : r.IsValid) (U : STLInterval ℝ) (hs : l.until U r = some s) (t : ℝ)
        (ht : 0 ≤ t) : -- --- CONCL ---
    s.at t = FourValued.join
        (((l.toKleeneSignal Kleene.ff).until U (r.toKleeneSignal Kleene.ff)).at t)
      (((l.toKleeneSignal Kleene.tt).until U (r.toKleeneSignal Kleene.tt)).at t)
    := by -- --- PROOF ---
  obtain ⟨s', hs', -, h⟩ := FourValuedSignal.until_spec l r hl hr U
  rw [hs] at hs'; cases hs'
  obtain ⟨h1, h2, -, -⟩ := h t ht
  unfold FourValued.join
  split_ifs with he
  · exact h2 he
  · exact h1.2 he


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSignal.until_refines (l r l' r' : FourValuedSignal ℝ) (hl : l.IsValid)
    (hr : r.IsValid) (hl' : l'.IsValid) (hr' : r'.IsValid) (U : STLInterval ℝ) : -- --- CONCL ---
    ∃ s s', l.until U r = some s ∧ l'.until U r' = some s' ∧ s.IsValid ∧ s'.IsValid ∧
      (l'.Refines l → r'.Refines r → s'.Refines s) ∧ ∀ t : ℝ, 0 ≤ t →
          (∀ x, t ≤ x → l.at x = l'.at x ∧ r.at x = r'.at x) →
        s.at t = s'.at t := by -- --- PROOF ---
  obtain ⟨s, hs, hsv, -⟩ := FourValuedSignal.until_spec l r hl hr U
  obtain ⟨s', hs', hsv', -⟩ := FourValuedSignal.until_spec l' r' hl' hr' U
  -- the refinements are valid and ordered
  have vlf := (l.toKleeneSignal_spec hl Kleene.ff).1
  have vlt := (l.toKleeneSignal_spec hl Kleene.tt).1
  have vrf := (r.toKleeneSignal_spec hr Kleene.ff).1
  have vrt := (r.toKleeneSignal_spec hr Kleene.tt).1
  have vlf' := (l'.toKleeneSignal_spec hl' Kleene.ff).1
  have vlt' := (l'.toKleeneSignal_spec hl' Kleene.tt).1
  have vrf' := (r'.toKleeneSignal_spec hr' Kleene.ff).1
  have vrt' := (r'.toKleeneSignal_spec hr' Kleene.tt).1
  refine ⟨s, s', hs, hs', hsv, hsv', ?_, ?_⟩
  · -- refinement: each of the three Kleene untils is monotone in its operands
    intro h1 h2 t ht hne
    have m1 := KleeneSignal.until_mono _ _ _ _ vlf vlf' vrf vrf' U
      (fun x hx => by
        rw [(l.toKleeneSignal_at hl x hx).1, (l'.toKleeneSignal_at hl' x hx).1]
        exact (aux_floor_ceil_of_refines _ _ (h1 x hx)).1)
      (fun x hx => by
        rw [(r.toKleeneSignal_at hr x hx).1, (r'.toKleeneSignal_at hr' x hx).1]
        exact (aux_floor_ceil_of_refines _ _ (h2 x hx)).1) t ht
    have m2 := KleeneSignal.until_mono _ _ _ _ vlf' vlt' vrf' vrt' U
      (fun x hx => by
        rw [(l'.toKleeneSignal_at hl' x hx).1, (l'.toKleeneSignal_at hl' x hx).2]
        exact aux_floor_le_ceil _)
      (fun x hx => by
        rw [(r'.toKleeneSignal_at hr' x hx).1, (r'.toKleeneSignal_at hr' x hx).2]
        exact aux_floor_le_ceil _) t ht
    -- and the refined ceiling below the old one
    have m3 := KleeneSignal.until_mono _ _ _ _ vlt' vlt vrt' vrt U
      (fun x hx => by
        rw [(l.toKleeneSignal_at hl x hx).2, (l'.toKleeneSignal_at hl' x hx).2]
        exact (aux_floor_ceil_of_refines _ _ (h1 x hx)).2)
      (fun x hx => by
        rw [(r.toKleeneSignal_at hr x hx).2, (r'.toKleeneSignal_at hr' x hx).2]
        exact (aux_floor_ceil_of_refines _ _ (h2 x hx)).2) t ht
    -- the four-valued until is the join of the floor and ceiling untils
    rw [aux_until_at_eq_join l r s hl hr U hs t ht] at hne ⊢
    rw [aux_until_at_eq_join l' r' s' hl' hr' U hs' t ht]
    unfold FourValued.join at hne ⊢
    split_ifs at hne with he
    · -- a conclusive value: floor and ceiling agree, and the refined ones are squeezed between
      have e1 : ((l'.toKleeneSignal Kleene.ff).until U (r'.toKleeneSignal Kleene.ff)).at t =
          ((l.toKleeneSignal Kleene.ff).until U (r.toKleeneSignal Kleene.ff)).at t :=
        le_antisymm (by rw [he]; exact m2.trans m3) m1
      have e2 : ((l'.toKleeneSignal Kleene.tt).until U (r'.toKleeneSignal Kleene.tt)).at t =
          ((l.toKleeneSignal Kleene.ff).until U (r.toKleeneSignal Kleene.ff)).at t :=
        le_antisymm (by rw [he]; exact m3) (m1.trans m2)
      rw [if_pos (e1.trans e2.symm), e1, if_pos he]
    · exact absurd rfl hne
  · intro t ht hagree
    rw [aux_until_at_eq_join l r s hl hr U hs t ht,
      aux_until_at_eq_join l' r' s' hl' hr' U hs' t ht]
    -- the refinements agree from `t` on, and the until at `t` only reads those times
    have key : ∀ (v : Kleene) (a b a' b' : KleeneSignal ℝ), a.IsValid → b.IsValid → a'.IsValid →
        b'.IsValid → (∀ x, t ≤ x → a.at x = a'.at x ∧ b.at x = b'.at x) →
        (a.until U b).at t = (a'.until U b').at t := by
      intro _ a b a' b' va vb va' vb' hab
      obtain ⟨-, hk⟩ := KleeneSignal.until_spec a b va vb U
      obtain ⟨-, hk'⟩ := KleeneSignal.until_spec a' b' va' vb' U
      obtain ⟨k1, k2⟩ := hk t ht
      obtain ⟨k1', k2'⟩ := hk' t ht
      have hge : ∀ t', t' - t ∈ U.set → t ≤ t' := fun t' h' => by
        have := STLInterval.zero_le_of_mem_set U _ h'; linarith
      -- the witness and the guard of the until lie at times `≥ t`
      apply aux_kleene_eq_of_iff
      · rw [k1, k1']
        constructor
        · rintro ⟨t', h1, h2, h3⟩
          refine ⟨t', h1, by rw [← (hab t' (hge t' h1)).2]; exact h2, fun x hx1 hx2 => ?_⟩
          rw [← (hab x hx1.le).1]; exact h3 x hx1 hx2
        · rintro ⟨t', h1, h2, h3⟩
          refine ⟨t', h1, by rw [(hab t' (hge t' h1)).2]; exact h2, fun x hx1 hx2 => ?_⟩
          rw [(hab x hx1.le).1]; exact h3 x hx1 hx2
      · rw [k2, k2']
        constructor
        · intro h t' h1
          rcases h t' h1 with h | ⟨x, hx1, hx2, hx3⟩
          · left; rw [← (hab t' (hge t' h1)).2]; exact h
          · right; exact ⟨x, hx1, hx2, by rw [← (hab x hx1.le).1]; exact hx3⟩
        · intro h t' h1
          rcases h t' h1 with h | ⟨x, hx1, hx2, hx3⟩
          · left; rw [(hab t' (hge t' h1)).2]; exact h
          · right; exact ⟨x, hx1, hx2, by rw [(hab x hx1.le).1]; exact hx3⟩
    -- the refinements of the operands agree from `t` on
    have agree : ∀ v : Kleene, ∀ x, t ≤ x → (l.toKleeneSignal v).at x = (l'.toKleeneSignal v).at x ∧
        (r.toKleeneSignal v).at x = (r'.toKleeneSignal v).at x := by
      intro v x hx
      have hx0 : 0 ≤ x := ht.trans hx
      obtain ⟨a1, a2⟩ := (l.toKleeneSignal_spec hl v).2 x hx0
      obtain ⟨b1, b2⟩ := (l'.toKleeneSignal_spec hl' v).2 x hx0
      obtain ⟨c1, c2⟩ := (r.toKleeneSignal_spec hr v).2 x hx0
      obtain ⟨d1, d2⟩ := (r'.toKleeneSignal_spec hr' v).2 x hx0
      obtain ⟨e1, e2⟩ := hagree x hx
      constructor
      · by_cases h : l.at x = FourValued.ii
        · rw [a1 h, b1 (e1 ▸ h)]
        · rw [a2 h, b2 (e1 ▸ h), e1]
      · by_cases h : r.at x = FourValued.ii
        · rw [c1 h, d1 (e2 ▸ h)]
        · rw [c2 h, d2 (e2 ▸ h), e2]
    rw [key Kleene.ff _ _ _ _ vlf vrf vlf' vrf' (agree Kleene.ff),
      key Kleene.tt _ _ _ _ vlt vrt vlt' vrt' (agree Kleene.tt)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
