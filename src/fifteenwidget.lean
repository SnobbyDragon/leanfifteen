import fifteen fifteentactics

open fifteen fifteen.tile fifteen.position
open widget widget.html widget.attr
open tactic fifteentactics

variable {α : Type}

/-
  As always...
  DUOLINGO COLORS ARE AESTHETIC <3
  https://design.duolingo.com/identity/color

  goal_position will be a rainbow :)
-/
inductive color : Type
| cardinal -- red
| fox -- orange
| bee -- yellow
| mask_green -- green
| macaw -- blue
| beetle -- purple
| wolf -- dark mode background
| white -- light mode background

open color

instance : has_to_string color :=
  ⟨ λ c, match c with
      | cardinal := "#ff4b4b"
      | fox := "#ff9600"
      | bee := "#ffc800"
      | mask_green := "#89e219"
      | macaw := "#1cb0f6"
      | beetle := "#ce82ff"
      | wolf := "#777777"
      | white := "#ffffff"
    end
  ⟩

-- TASTE THE RAINBOW !
def tile_colors' : fin 16 → color
| ⟨0,_⟩ := wolf -- empty tile in dark mode
| ⟨1,_⟩ := cardinal
| ⟨2,_⟩ := fox --| ⟨5,_⟩ := fox
| ⟨3,_⟩ := bee --| ⟨6,_⟩ := bee | ⟨9,_⟩ := bee
| ⟨4,_⟩ := mask_green --| ⟨7,_⟩ := mask_green | ⟨10,_⟩ := mask_green | ⟨13,_⟩ := mask_green
| ⟨8,_⟩ := macaw --| ⟨11,_⟩ := macaw | ⟨14,_⟩ := macaw
| ⟨12,_⟩ := beetle --| ⟨15,_⟩ := beetle
| ⟨n+3,_⟩ := tile_colors' ⟨n,by linarith⟩ using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf subtype.val⟩]}

def tile_colors (t : tile) (p : position) : color := tile_colors' $ p.map t

-- raised tile look :)
def tile_border_styles (t : tile) (p : position) : string :=
if hole t p then "none" else "outset"

def tile_border_widths' : tile → string
| aa := "3px 1px 1px 3px" -- top left corner
| ab := "3px 1px 1px 1px" | ac := "3px 1px 1px 1px" -- top edges
| ad := "3px 3px 1px 1px" -- top right corner
| bd := "1px 3px 1px 1px" | cd := "1px 3px 1px 1px" -- right edges
| dd := "1px 3px 3px 1px" -- bottom right corner
| dc := "1px 1px 3px 1px" | db := "1px 1px 3px 1px" -- bottom edges
| da := "1px 1px 3px 3px" -- bottom left corner
| ca := "1px 1px 1px 3px" | ba := "1px 1px 1px 3px"  -- left edges
| _ := "1px" -- inner

-- TODO: need higher outset near empty tile; need to calculate edges bordering empty tile
def tile_border_widths (t : tile) (p : position) : string := tile_border_widths' t

meta def tile_text (t : tile) (p : position) : string :=
if hole t p then "" else to_string $ p.map t

section static

meta def tile_html (t : tile) (p : position) : html empty :=
h "div" [
  style [
    ("background-color", to_string $ tile_colors t p),
    ("width", "50px"),
    ("height", "50px"),
    ("border-color", to_string white),
    ("border-style", tile_border_styles t p),
    ("border-width", tile_border_widths t p),
    ("text-align", "center"),
    ("line-height", "45px"),
    ("color", to_string white),
    ("font", "24px Comic Sans MS") -- THE BEST FONT
  ]
] [tile_text t p]

meta def tiles_html (p : position) : list (html empty) :=
list.map (λ t : tile, tile_html t p) tiles_list

meta def position_html (p : position) : html empty :=
h "div" [
  style [
    ("display", "grid"),
    ("grid-template", "repeat(4, 1fr) / repeat(4, 1fr)"),
    ("width", "200px")
  ]
] (tiles_html p)

#html position_html goal_position

meta def solved : tactic (list (html empty)) :=
do { gs ← get_goals,
     if gs.length = 0 then return [widget_override.goals_accomplished_message]
     else tactic.fail "there are still goals!"
} <|> tactic.fail "bad vibes"

meta def fifteen_widget : tactic (list (html empty)) :=
do { p ← get_position,
     return [position_html p]
} <|> solved

meta def fifteen_component : tc unit empty := tc.stateless (λ u, fifteen_widget)

meta def fifteen_save_info (p : pos) : tactic unit :=
do tactic.save_widget p (widget.tc.to_component fifteen_component)

end static

section interactive

meta def tile_html' (t : tile) (p : position) : html tile :=
h "div" [
  style [
    ("background-color", to_string $ tile_colors t p),
    ("width", "50px"),
    ("height", "50px"),
    ("border-color", to_string white),
    ("border-style", tile_border_styles t p),
    ("border-width", tile_border_widths t p),
    ("text-align", "center"),
    ("line-height", "45px"),
    ("color", to_string white),
    ("font", "24px Comic Sans MS") -- THE BEST FONT
  ],
  on_click (λ x, t)
] [tile_text t p]

meta def tiles_html' (p : position) : list (html tile) :=
list.map (λ t : tile, widget.html.map_action (λ t', t') (tile_html' t p)) tiles_list

meta def position_html' (p : position) : html tile :=
h "div" [
  style [
    ("display", "grid"),
    ("grid-template", "repeat(4, 1fr) / repeat(4, 1fr)"),
    ("width", "200px")
  ]
] (tiles_html' p)

meta inductive fifteen_action
| click_tile (t : tile)

open fifteen_action

meta def fifteen_view : position → list (html fifteen_action)
| p := [widget.html.map_action click_tile $ position_html' p]

meta def fifteen_update : position → fifteen_action → position × option widget.effects
| p (click_tile t) := (p, some [effect.insert_text $ "slide_tile " ++ to_string t ++ ","])

meta def fifteen_init : unit → tactic position
| () := do get_position

meta def fifteen_component' : tc unit empty :=
component.ignore_action
$ component.with_effects (λ _ e, e)
$ tc.mk_simple fifteen_action position fifteen_init (λ _ p a, pure $ fifteen_update p a) (λ _ p, pure $ fifteen_view p)

meta def fifteen_save_info' (p : pos) : tactic unit :=
do tactic.save_widget p (widget.tc.to_component fifteen_component')

end interactive