import fifteen fifteentactics

open fifteen fifteen.tile fifteen.position
open widget widget.html widget.attr
open tactic fifteentactics

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

open color

instance : has_to_string color :=
  ⟨ λ c, match c with
      | cardinal := "#ff4b4b"
      | fox := "#ff9600"
      | bee := "#ffc800"
      | mask_green := "#89e219"
      | macaw := "#1cb0f6"
      | beetle := "#ce82ff"
    end
  ⟩

