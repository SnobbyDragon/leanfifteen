import fifteen

open fifteen fifteen.tile fifteen.position
open tactic

namespace fifteentactics

-- just unfolds game
meta def start_game : tactic unit :=
do { `(game %%d) ← tactic.target,
     dunfold_target [``game]
} <|> tactic.fail "not a game !"

-- given the list of adjacent tiles, finds the empty one
meta def find_adj_empty (p : position) : list tile → tactic tile
| [] := tactic.fail "all adjacent tiles are non-empty !"
| (t :: adj) := if empty t p then return t else find_adj_empty adj

-- gets the adjacent empty tile
meta def get_adj_empty (t : tile) (p : position) : tactic tile :=
do { let adj := get_adjacent t,
     e ← find_adj_empty p adj,
     return e
} <|> tactic.fail "all adjacent tiles are non-empty !"

meta def slide_tile (t : tile) : tactic unit :=
do { `(can_slide_to %%p₁ %%p₂) ← tactic.target,
     `[apply can_slide_to.can_slide_to_one],
     p ← (eval_expr position) p₁,
     e ← get_adj_empty t p,
     tactic.trace $ "The empty tile is " ++ to_string e,
     tactic.target >>= tactic.trace,
     `[use [t, e]]
} <|> tactic.fail "failed to slide tile :("



end fifteentactics