import fifteen

open fifteen fifteen.tile fifteen.position
open tactic

namespace fifteentactics

-- just unfolds game
meta def start_game : tactic unit :=
do { `(game %%d) ← tactic.target,
     dunfold_target [``game]
} <|> tactic.fail "not a game !"

meta def get_start_position : tactic position :=
do { dunfold_target [``game],
     `(can_slide_to %%p₁ %%p₂) ← tactic.target,
     p ← (eval_expr position) p₁,
     return p
} <|> tactic.fail "failed to get current position"

meta def get_position : tactic position :=
do { `(can_slide_to %%p₁ %%p₂) ← tactic.target,
     p ← (eval_expr position) p₁,
     return p
} <|> get_start_position

-- given a list of tiles, finds the hole
meta def find_hole (p : position) : list tile → tactic tile
| [] := tactic.fail "failed to find empty tile !"
| (t :: lt) := if hole t p then return t else find_hole lt

-- gets the adjacent hole
meta def get_adj_hole (t : tile) (p : position) : tactic tile :=
do { let adj := get_adjacent t,
     e ← find_hole p adj,
     return e
} <|> tactic.fail "no adjacent hole !"

-- gets tiles adjacent to the hole
meta def get_hole_adj (p : position) : tactic (list tile) :=
do { let tiles := tiles_list,
     e ← find_hole p tiles,
     return $ get_adjacent e
} <|> tactic.fail "apparently there's no hole"

meta def slide_tile (t : tile) : tactic unit :=
do { p ← get_position,
     `[apply slide_one_step],
     e ← get_adj_hole t p,
    --  tactic.trace $ "Want to slide " ++ to_string t ++ " to " ++ to_string e,
    --  tactic.target >>= tactic.trace,
     tactic.interactive.use [pexpr.of_expr (reflect t), pexpr.of_expr (reflect e)],
     `[split, split; dec_trivial]
} <|> tactic.fail "failed to slide tile :("

end fifteentactics