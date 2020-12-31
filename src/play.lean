import fifteen puzzles fifteentactics

open fifteen fifteen.tile fifteen.position
open puzzles fifteentactics

/-
  Here ye play games :)
-/

example : game puzzle_1 :=
begin
  unfold game,
  apply can_slide_to.can_slide_to_one,
  use [bc, bd],
  sorry
end

example : game puzzle_1 :=
begin
  start_game,
  slide_tile bc,
end