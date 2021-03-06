import tactic

namespace fifteen
/-
  You take a deep breath
  And you walk through the doors
  It's the morning of your very first day
  ...
-/

section defenestration -- definitions

-- why in the world did I use an enumerated type instead of fin 4 × fin 4?
-- unfortunately this way is not easily scalable to other dimensions
-- at least it looks pretty :)
@[derive [decidable_eq, has_reflect, fintype]]
inductive tile : Type
| aa | ab | ac | ad
| ba | bb | bc | bd
| ca | cb | cc | cd
| da | db | dc | dd
-- not really using fintype rn but it's there anyways

open tile

instance : has_to_string tile :=
⟨ λ t, match t with
  | aa := "aa"
  | ab := "ab"
  | ac := "ac"
  | ad := "ad"
  | ba := "ba"
  | bb := "bb"
  | bc := "bc"
  | bd := "bd"
  | ca := "ca"
  | cb := "cb"
  | cc := "cc"
  | cd := "cd"
  | da := "da"
  | db := "db"
  | dc := "dc"
  | dd := "dd"
  end
⟩

-- TODO: use `fin_range` and `univ` ?
def tiles_list : list tile := [aa, ab, ac, ad, ba, bb, bc, bd, ca, cb, cc, cd, da, db, dc, dd]

def get_adjacent : tile → list tile
| aa := [ab, ba]
| ab := [aa, ac, bb]
| ac := [ab, ad, bc]
| ad := [ac, bd]
| ba := [aa, bb, ca]
| bb := [ab, ba, bc, cb]
| bc := [ac, bb, bd, cc]
| bd := [ad, bc, cd]
| ca := [ba, cb, da]
| cb := [bb, ca, cc, db]
| cc := [bc, cb, cd, dc]
| cd := [bd, cc, dd]
| da := [ca, db]
| db := [cb, da, dc]
| dc := [cc, db, dd]
| dd := [cd, dc]

def is_adjacent (t₁ t₂ : tile) : Prop := t₁ ∈ (get_adjacent t₂)

@[ext] structure position := 
(map : tile → fin 16)
-- (bij : function.bijective map)
-- don't know if bijective is helpful,
-- but it makes things more complicated so taking it out for now

-- Mario Carneiro's Magic!
-- I still don't know what @[ext] and this instance does...
instance : decidable_eq position :=
λ a b, decidable_of_iff' _ (position.ext_iff _ _)

-- zero denotes the hole
@[derive decidable]
def hole (t : tile) (p : position) : Prop := p.map t = 0

def valid_slide' (t : tile) (p : position) : Prop :=
∃ t' ∈ get_adjacent t, hole t' p

def valid_slide (t h : tile) (p : position) : Prop :=
h ∈ get_adjacent t ∧ hole h p

def slide (t h : tile) (p : position) : position :=
⟨ λ t',
  if t' = t then p.map h
  else if t' = h then p.map t
  else p.map t'
⟩

def goal_position : position :=
⟨ λ t, match t with
  | aa := 1 | ab := 2 | ac := 3 | ad := 4
  | ba := 5 | bb := 6 | bc := 7 | bd := 8
  | ca := 9 | cb := 10| cc := 11| cd := 12
  | da := 13| db := 14| dc := 15| dd := 0
  end 
⟩

#eval goal_position.map dc
#eval (slide dc dd goal_position).map dc

-- this is really lookin like hanoi but with sliding
inductive can_slide_to : position → position → Prop
| self : ∀ (p : position), can_slide_to p p
| one : ∀ (p₁ p₂ : position), (∃ (t e : tile), (valid_slide t e p₁) ∧ (slide t e p₁) = p₂) → can_slide_to p₁ p₂
| trans : ∀ (p₁ p₂ p₃ : position), can_slide_to p₁ p₂ → can_slide_to p₂ p₃ → can_slide_to p₁ p₃

-- we are assuming start is a solvable position
def game (start : position) := can_slide_to start goal_position

end defenestration

section limabeans -- lemmas

-- symmetry for adjacency
lemma sym_adj (t₁ t₂ : tile) : is_adjacent t₁ t₂ ↔ is_adjacent t₂ t₁ :=
begin
  split; intros h; cases t₁; cases t₂; try {exact h},
  all_goals {unfold is_adjacent at *; unfold get_adjacent at *; try {dec_trivial} },
  all_goals { exfalso; finish },
end

lemma slide_one_step (p₁ p₂ : position) : (∃ (t e : tile), (valid_slide t e p₁) ∧ can_slide_to (slide t e p₁) p₂) → can_slide_to p₁ p₂ :=
begin
  rintros ⟨t, e, h₁, h₂⟩,
  apply can_slide_to.trans p₁ (slide t e p₁) p₂,
  apply can_slide_to.one,
  use [t, e],
  split,
  { exact h₁ },
  { refl },
  exact h₂,
end

-- more of Mario Carneiro's Magic
lemma can_slide_to.of_eq : ∀ {p₁ p₂ : position} (h : p₁ = p₂), can_slide_to p₁ p₂
| p _ rfl := can_slide_to.self p

end limabeans

end fifteen