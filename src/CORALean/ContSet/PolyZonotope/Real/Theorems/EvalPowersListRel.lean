module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPowersList
public import Mathlib.Data.List.Forall2

@[expose] public section

/-!
# `PolyZonotope.evalPowersList` keeps every relation its arithmetic keeps

If a relation `R` holds between the constants of two `PowerOps` and every sum and product keeps
it, then it holds between the two results entry by entry, given that it holds between the
coefficients and between the rows. This is how the float run (midpoint and radius) is read as the
real one, coordinate by coordinate, and how the lengths of two runs are seen to agree (`R` true).

## Inputs
* `o` – first arithmetic
* `o'` – second arithmetic
* `R` – relation between their scalars
* `as` – coefficients in the first
* `as'` – coefficients in the second
* `x` – row in the first
* `y` – row in the second

## Hypotheses
* `hzero` – `R` relates the zeros
* `htwo` – `R` relates the twos
* `hhalf` – `R` relates the halves
* `hadd` – sums keep `R`
* `hmul` – products keep `R`
* `has` – `R` relates the coefficients
* `hc` – `R` relates the centers
* `hG` – `R` relates the dependent generators
* `hGI` – `R` relates the independent generators

## Conclusion
* `R` relates the centers and the generators of the two results
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ δ ε ζ : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {o : PowerOps α} {o' : PowerOps β} {R : α → β → Prop}

/-- Two sets of operations related: the constants by `R`, and `R` preserved by both operations. -/
private structure aux_OpsRel (R : α → β → Prop) (o : PowerOps α) (o' : PowerOps β) : Prop where
  zero : R o.zero o'.zero
  two : R o.two o'.two
  half : R o.half o'.half
  add {a a' b b'} : R a a' → R b b' → R (o.add a b) (o'.add a' b')
  mul {a a' b b'} : R a a' → R b b' → R (o.mul a b) (o'.mul a' b')

/-- Two rows related entry by entry. -/
private structure aux_RowRel (R : α → β → Prop) (x : PowerRow α) (y : PowerRow β) : Prop where
  c : R x.c y.c
  G : List.Forall₂ R x.G y.G
  GI : List.Forall₂ R x.GI y.GI

/-- A map preserves a relation that the function carries. -/
private theorem aux_rel_map {S : α → β → Prop} {f : α → γ} {g : β → δ} {T : γ → δ → Prop}
    (hf : ∀ a b, S a b → T (f a) (g b)) {l : List α} {l' : List β} (h : List.Forall₂ S l l') :
    List.Forall₂ T (l.map f) (l'.map g) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hab _ ih => exact List.Forall₂.cons (hf _ _ hab) ih

/-- `crossWith` preserves a relation that the function carries. -/
private theorem aux_rel_cross {S : α → β → Prop} {S' : γ → δ → Prop} {T : ε → ζ → Prop}
    {f : α → γ → ε} {g : β → δ → ζ} (hf : ∀ a b c d, S a b → S' c d → T (f a c) (g b d))
    {a : List α} {a' : List β} {b : List γ} {b' : List δ}
    (ha : List.Forall₂ S a a') (hb : List.Forall₂ S' b b') : -- --- CONCL ---
    List.Forall₂ T (PolyZonotope.crossWith f a b)
        (PolyZonotope.crossWith g a' b') := by -- --- PROOF ---
  induction hb with
  | nil => exact List.Forall₂.nil
  | cons hcd _ ih =>
    simp only [PolyZonotope.crossWith, List.flatMap_cons] at ih ⊢
    exact List.rel_append (aux_rel_map (fun x y hxy => hf _ _ _ _ hxy hcd) ha) ih

/-- `pairsWith` preserves a relation that the function carries. -/
private theorem aux_rel_pairs {S : α → β → Prop} {T : γ → δ → Prop} {f : α → α → γ} {g : β → β → δ}
    (hf : ∀ a b c d, S a b → S c d → T (f a c) (g b d)) {a : List α} {a' : List β}
    (ha : List.Forall₂ S a a') : -- --- CONCL ---
    List.Forall₂ T (PolyZonotope.pairsWith f a) (PolyZonotope.pairsWith g a') := by -- --- PROOF ---
  induction ha with
  | nil => exact List.Forall₂.nil
  | cons hab hr ih =>
    simp only [PolyZonotope.pairsWith]
    exact List.rel_append (aux_rel_map (fun x y hxy => hf _ _ _ _ hab hxy) hr) ih

/-- A left fold preserves a relation that the step carries. -/
private theorem aux_rel_foldl {S : α → β → Prop} {T : γ → δ → Prop} {f : γ → α → γ} {g : δ → β → δ}
    (hf : ∀ a b c d, T a b → S c d → T (f a c) (g b d)) {l : List α} {l' : List β}
    (h : List.Forall₂ S l l') {z : γ} {z' : δ} (hz : T z z') :
    T (l.foldl f z) (l'.foldl g z') := by
  induction h generalizing z z' with
  | nil => exact hz
  | cons hab _ ih => exact ih (hf _ _ _ _ hz hab)

/-- `zipWith` preserves a relation that the function carries. -/
private theorem aux_rel_zipWith {S : α → β → Prop} {T : γ → δ → Prop} {U : ε → ζ → Prop}
    {f : α → γ → ε} {g : β → δ → ζ} (hf : ∀ a b c d, S a b → T c d → U (f a c) (g b d))
    {a : List α} {a' : List β} {b : List γ} {b' : List δ}
    (ha : List.Forall₂ S a a') (hb : List.Forall₂ T b b') : -- --- CONCL ---
    List.Forall₂ U (List.zipWith f a b) (List.zipWith g a' b') := by -- --- PROOF ---
  induction ha generalizing b b' with
  | nil => simp
  | cons hab _ ih =>
    cases hb with
    | nil => simp
    | cons hcd hb' => exact List.Forall₂.cons (hf _ _ _ _ hab hcd) (ih hb')


/-- The square step preserves the relation of the rows. -/
private theorem aux_rel_square (h : aux_OpsRel R o o') {x : PowerRow α} {y : PowerRow β}
    (hx : aux_RowRel R x y) : -- --- CONCL ---
    aux_RowRel R (PolyZonotope.step_square o x)
        (PolyZonotope.step_square o' y) := by -- --- PROOF ---
  have hsq := aux_rel_map (T := R) (fun a b hab => h.mul (h.mul hab hab) h.half) hx.GI
  have hpair : ∀ a b c d, R a b → R c d → R (o.mul (o.mul o.two a) c) (o'.mul (o'.mul o'.two b)
      d) :=
    fun _ _ _ _ hab hcd => h.mul (h.mul h.two hab) hcd
  refine ⟨aux_rel_foldl (S := R) (T := R) (fun _ _ _ _ h1 h2 => h.add h1 h2) hsq (h.mul hx.c hx.c),
    ?_, ?_⟩
  · exact List.rel_append (List.rel_append (List.rel_append
      (aux_rel_map (fun _ _ hab => h.mul hx.c hab) hx.G) (aux_rel_map (fun _ _ hab => h.mul hx.c
          hab) hx.G))
      (aux_rel_map (fun _ _ hab => h.mul hab hab) hx.G)) (aux_rel_pairs hpair hx.G)
  · exact List.rel_append (List.rel_append (List.rel_append (List.rel_append
      (aux_rel_map (fun _ _ hab => h.mul hx.c hab) hx.GI) (aux_rel_map (fun _ _ hab => h.mul hx.c
          hab) hx.GI))
      hsq) (aux_rel_pairs hpair hx.GI))
      (aux_rel_map (fun _ _ hab => h.mul h.two hab)
        (aux_rel_cross (T := R) (f := o.mul) (g := o'.mul) (fun _ _ _ _ h1 h2 => h.mul h1 h2) hx.GI
            hx.G))

/-- The product step preserves the relation of the rows. -/
private theorem aux_rel_times (h : aux_OpsRel R o o') {x x' : PowerRow α} {y y' : PowerRow β}
    (hx : aux_RowRel R x y)
    (hx' : aux_RowRel R x' y') : -- --- CONCL ---
    aux_RowRel R (PolyZonotope.step_times o x x')
        (PolyZonotope.step_times o' y y') := by -- --- PROOF ---
  have hm : ∀ a b c d, R a b → R c d → R (o.mul a c) (o'.mul b d) := fun _ _ _ _ => h.mul
  refine ⟨h.mul hx.c hx'.c, ?_, ?_⟩
  · exact List.rel_append (List.rel_append
      (aux_rel_map (fun _ _ hab => h.mul hx'.c hab) hx.G) (aux_rel_map (fun _ _ hab => h.mul hx.c
          hab) hx'.G))
      (aux_rel_cross hm hx.G hx'.G)
  · exact List.rel_append (List.rel_append (List.rel_append (List.rel_append
      (aux_rel_map (fun _ _ hab => h.mul hx'.c hab) hx.GI)
      (aux_rel_map (fun _ _ hab => h.mul hx.c hab) hx'.GI))
      (aux_rel_cross hm hx.GI hx'.GI)) (aux_rel_cross hm hx.G hx'.GI)) (aux_rel_cross hm hx.GI
          hx'.G)

/-- Every power preserves the relation of the rows. -/
private theorem aux_rel_power (h : aux_OpsRel R o o') {x : PowerRow α} {y : PowerRow β}
    (hx : aux_RowRel R x y) (i : ℕ) : -- --- CONCL ---
    aux_RowRel R (PolyZonotope.step_power o x i)
        (PolyZonotope.step_power o' y i) := by -- --- PROOF ---
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rw [PolyZonotope.step_power.eq_1 o x i, PolyZonotope.step_power.eq_1 o' y i]
    split_ifs with h1 h2
    · exact hx
    · exact aux_rel_square h (ih _ (by omega))
    · exact aux_rel_times h (ih _ (by omega)) (ih _ (by omega))


/-- Related lists have related entries, the default included. -/
private theorem aux_rel_getD (h : aux_OpsRel R o o') {l : List α} {l' : List β} (hl : List.Forall₂
    R l l') (i : ℕ) : -- --- CONCL ---
    R (l.getD i o.zero) (l'.getD i o'.zero) := by -- --- PROOF ---
  induction hl generalizing i with
  | nil => exact h.zero
  | cons hab _ ih => cases i with
    | zero => exact hab
    | succ i => exact ih i

/-- Folding one power into its factors preserves the relation. -/
private theorem aux_rel_foldAt (h : aux_OpsRel R o o') {len : ℕ → ℕ} {W : ℕ → List α} {W' : ℕ →
    List β}
    (hW : ∀ j, List.Forall₂ R (W j) (W' j)) (i : ℕ) : -- --- CONCL ---
    ∀ j, List.Forall₂ R (PolyZonotope.step_foldAt o len W i j) (PolyZonotope.step_foldAt o' len W'
        i j) := by -- --- PROOF ---
  intro j
  simp only [PolyZonotope.step_foldAt, Function.update_apply]
  have hadd : ∀ a b c d, R a b → R c d → R (o.add a c) (o'.add b d) := fun _ _ _ _ => h.add
  have hP1 := List.forall₂_take (len (i / 2)) (hW i)
  have hP2 := List.forall₂_take (len ((i + 1) / 2)) (List.forall₂_drop (len (i / 2)) (hW i))
  split_ifs <;> first
    | exact aux_rel_zipWith hadd (aux_rel_zipWith hadd (hW _) hP1) hP2
    | exact aux_rel_zipWith hadd (hW _) hP2
    | exact aux_rel_zipWith hadd (hW _) hP1
    | exact hW j

/-- Folding all powers down preserves the relation. -/
private theorem aux_rel_foldDown (h : aux_OpsRel R o o') {len : ℕ → ℕ} {W : ℕ → List α} {W' : ℕ →
    List β}
    (hW : ∀ j, List.Forall₂ R (W j) (W' j)) (k : ℕ) : -- --- CONCL ---
    ∀ j, List.Forall₂ R (PolyZonotope.step_foldDown o len W k j) (PolyZonotope.step_foldDown o' len
        W' k j) := by -- --- PROOF ---
  induction k using Nat.strong_induction_on generalizing W W' with
  | _ k ih =>
    match k with
    | 0 => exact hW
    | 1 => exact hW
    | k + 2 =>
      simp only [PolyZonotope.step_foldDown]
      exact ih (k + 1) (by omega) (aux_rel_foldAt h hW (k + 2))

/-- The own parts of related powers are related. -/
private theorem aux_rel_own {len : ℕ → ℕ} {F : ℕ → List α} {F' : ℕ → List β}
    (hF : ∀ j, List.Forall₂ R (F j) (F' j)) (k : ℕ) : -- --- CONCL ---
    List.Forall₂ R (PolyZonotope.powerParts len F k)
        (PolyZonotope.powerParts len F' k) := by -- --- PROOF ---
  unfold PolyZonotope.powerParts
  refine List.rel_append (hF 1) ?_
  induction (List.range' 2 (k - 1)) with
  | nil => exact List.Forall₂.nil
  | cons i r ih =>
    simp only [List.flatMap_cons]
    exact List.rel_append (List.forall₂_drop _ (hF i)) ih

/-- The whole run preserves the relation. -/
private theorem aux_rel_evalPowersList (h : aux_OpsRel R o o') {as : List α} {as' : List β}
    (has : List.Forall₂ R as as')
    {x : PowerRow α} {y : PowerRow β} (hx : aux_RowRel R x y) : -- --- CONCL ---
    aux_RowRel R (PolyZonotope.evalPowersList o as x)
        (PolyZonotope.evalPowersList o' as' y) := by -- --- PROOF ---
  have hlen : as.length = as'.length := has.length_eq
  have hX := aux_rel_power h hx
  have hW : ∀ i, aux_RowRel R (PolyZonotope.step_weigh o (as.getD i o.zero)
      (PolyZonotope.step_power o x i))
      (PolyZonotope.step_weigh o' (as'.getD i o'.zero) (PolyZonotope.step_power o' y i)) := fun i =>
    ⟨h.mul (hX i).c (aux_rel_getD h has i),
      aux_rel_map (fun _ _ hab => h.mul hab (aux_rel_getD h has i)) (hX i).G,
      aux_rel_map (fun _ _ hab => h.mul hab (aux_rel_getD h has i)) (hX i).GI⟩
  -- the weighed powers are related, and so are their lengths
  have hlG : (fun i => (PolyZonotope.step_power o x i).G.length) =
      fun i => (PolyZonotope.step_power o' y i).G.length :=
    funext fun i => (hX i).G.length_eq
  have hlGI : (fun i => (PolyZonotope.step_power o x i).GI.length) =
      fun i => (PolyZonotope.step_power o' y i).GI.length :=
    funext fun i => (hX i).GI.length_eq
  -- the center by the fold of the weighed centers, the generators by the own parts
  simp only [PolyZonotope.evalPowersList, hlen, hlG, hlGI]
  refine ⟨h.add ?_ (aux_rel_getD h has 0), ?_, ?_⟩
  rotate_left
  · dsimp only
    exact aux_rel_own (aux_rel_foldDown h (fun j => (hW j).G) _) _
  · dsimp only
    exact aux_rel_own (aux_rel_foldDown h (fun j => (hW j).GI) _) _
  exact aux_rel_foldl (S := Eq) (T := R) (fun _ _ i _ hab hij => hij ▸ h.add hab (hW i).c)
    (List.forall₂_same.2 fun _ _ => rfl) h.zero

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.evalPowersList_rel {o : PowerOps α} {o' : PowerOps β} {R : α → β → Prop}
    (hzero : R o.zero o'.zero) (htwo : R o.two o'.two) (hhalf : R o.half o'.half)
    (hadd : ∀ {a a' b b'}, R a a' → R b b' → R (o.add a b) (o'.add a' b'))
    (hmul : ∀ {a a' b b'}, R a a' → R b b' → R (o.mul a b) (o'.mul a' b'))
    {as : List α} {as' : List β} (has : List.Forall₂ R as as') {x : PowerRow α}
    {y : PowerRow β} (hc : R x.c y.c) (hG : List.Forall₂ R x.G y.G)
    (hGI : List.Forall₂ R x.GI y.GI) : -- --- CONCL ---
    R (PolyZonotope.evalPowersList o as x).c (PolyZonotope.evalPowersList o' as' y).c
      ∧ List.Forall₂ R (PolyZonotope.evalPowersList o as x).G
        (PolyZonotope.evalPowersList o' as' y).G
      ∧ List.Forall₂ R (PolyZonotope.evalPowersList o as x).GI
        (PolyZonotope.evalPowersList o' as' y).GI := by -- --- PROOF ---
  have h := aux_rel_evalPowersList (aux_OpsRel.mk hzero htwo hhalf hadd hmul) has ⟨hc, hG, hGI⟩
  exact ⟨h.c, h.G, h.GI⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
