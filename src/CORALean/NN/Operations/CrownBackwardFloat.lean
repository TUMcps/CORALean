module

public import CORALean.NN.Definitions.CrownNetFloat

@[expose] public section

/-!
# `CrownNet.backward` in floats

CROWN's backward pass in CORA.cpp's order (`priv_backward_lower`), with what the rounding costs
charged beside it. Through an affine map the constant gains `ν · b` and the row becomes `Wᵀ ν`;
through an activation the constant gains `ν⁺ · b_l` and then `ν⁻ · b_u`, and the row becomes
`ν⁺ s_l + ν⁻ s_u`. The row is rounded down; its rounding error is at most the gap to the row
rounded up. A map passes the gap it receives through `|W|` and charges its share of `|b|`; an
activation charges the gap it receives at the bound of `|σ t|` between its lines, and its own
row's gap at the bound of `|t|` on its box. At nearest both directions round alike, so every gap
and the slack are `+0`, and the row and the constant are CORA.cpp's bit for bit.

## Inputs
* none

## Output
* the row on the inputs, its gap, the constant and the slack
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def CrownNet.backward : {n k : ℕ} → CrownNet 𝕋 n k → Vec 𝕋 k → CrownRow 𝕋 n
  | _, _, .nil, Λ => ⟨Λ, fun _ => zero, zero, zero⟩
  | _, _, .linear W b rest, Λ =>
    let ρ := rest.backward Λ
    -- 1. the constant gains `ν · b` (CORA.cpp: `constant + lam.multiply(b).sum(-1)`)
    let c := addDown ρ.const (dotDown ρ.row b)
    -- 2. the row becomes `Wᵀ ν` (CORA.cpp: `linear_t`), rounded down, with its rounding gap
    let μ : Vec 𝕋 _ := fun j => dotDown ρ.row fun i => W i j
    let e : Vec 𝕋 _ := fun j => subUp (dotUp ρ.row fun i => W i j) (μ j)
    -- 3. the gap received moves through `|W|`, and its share of `|b|` goes into the slack
    let g : Vec 𝕋 _ := fun j => addUp (dotUp ρ.gap fun i => absolute (W i j)) (e j)
    let s := addUp ρ.slack (dotUp ρ.gap fun i => absolute (b i))
    ⟨μ, g, c, s⟩
  | _, _, .act l u sl bl su bu rest, Λ =>
    let ρ := rest.backward Λ
    let p : Vec 𝕋 _ := fun i => maximum (ρ.row i) zero
    let q : Vec 𝕋 _ := fun i => minimum (ρ.row i) zero
    -- 1. the constant gains `ν⁺ · b_l`, then `ν⁻ · b_u` (CORA.cpp's order)
    let c := addDown (addDown ρ.const (dotDown p bl)) (dotDown q bu)
    -- 2. the row becomes `ν⁺ s_l + ν⁻ s_u`, rounded down, with its rounding gap
    let μ : Vec 𝕋 _ := fun i => addDown (mulDown (p i) (sl i)) (mulDown (q i) (su i))
    let e : Vec 𝕋 _ := fun i => subUp (addUp (mulUp (p i) (sl i)) (mulUp (q i) (su i))) (μ i)
    -- 3. `|t|` on the box, and `|σ t|` between the lines there
    let m : Vec 𝕋 _ := fun i => maximum (absolute (l i)) (absolute (u i))
    let hb : Vec 𝕋 _ := fun i => maximum (addUp (mulUp (absolute (sl i)) (m i)) (absolute (bl i)))
      (addUp (mulUp (absolute (su i)) (m i)) (absolute (bu i)))
    -- 4. the gap received at `|σ t|`, the row's own gap at `|t|`
    let s := addUp (addUp ρ.slack (dotUp ρ.gap hb)) (dotUp e m)
    ⟨μ, fun _ => zero, c, s⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
