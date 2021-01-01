import fifteen

open fifteen fifteen.tile fifteen.position
open tactic tactic.interactive («have»)

namespace fifteentactics

-- just unfolds game
meta def start_game : tactic unit :=
do { dunfold_target [``game]
} <|> tactic.fail "not a game !"

meta def get_start_position : tactic position :=
do { start_game,
     `(can_slide_to %%p₁ %%p₂) ← tactic.target,
     p ← (eval_expr position) p₁,
     return p
} <|> tactic.fail "failed to get current position"

meta def get_position : tactic position :=
do { `(can_slide_to %%p₁ %%p₂) ← tactic.target,
     p ← (eval_expr position) p₁,
     return p
} <|> get_start_position

-- TODO follow easy_cheesy example
meta def finish_game : tactic unit :=
do { p ← get_position,
     «have» `H ``(%%p.map = goal_position.map) ``(by dec_trivial),
     tactic.skip
} <|> tactic.fail "we are not done !"

-- given a list of tiles, finds the hole
meta def find_hole (p : position) : list tile → tactic tile
| [] := tactic.fail "failed to find the hole !"
| (t :: lt) := if hole t p then return t else find_hole lt

-- gets the adjacent hole
meta def get_adj_hole (t : tile) (p : position) : tactic tile :=
do { let adj := get_adjacent t,
     h ← find_hole p adj,
     return h
} <|> tactic.fail "no adjacent hole !"

-- gets location of the hole
meta def get_hole (p : position) : tactic tile :=
do { let tiles := tiles_list,
     h ← find_hole p tiles,
     return h
} <|> tactic.fail "apparently there's no hole"

-- gets tiles adjacent to the hole
meta def get_hole_adj (p : position) : tactic (list tile) :=
do { h ← get_hole p,
     return $ get_adjacent h
} <|> tactic.fail "apparently there's no hole"

meta def slide_tile (t : tile) : tactic unit :=
do { p ← get_position,
     `[apply slide_one_step],
     h ← get_adj_hole t p,
    --  tactic.trace $ "Want to slide " ++ to_string t ++ " to " ++ to_string h,
    --  tactic.target >>= tactic.trace,
     tactic.interactive.use [pexpr.of_expr (reflect t), pexpr.of_expr (reflect h)],
     `[split, split; dec_trivial]
} <|> tactic.fail "failed to slide tile :("

end fifteentactics