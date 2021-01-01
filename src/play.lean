import fifteen puzzles fifteentactics fifteeninteractive

open fifteen fifteen.tile fifteen.position
open puzzles fifteentactics

/-
  Here ye play games :)
-/

example : game puzzle_1 :=
begin
  unfold game,
  apply slide_one_step,
  use [bc, bd],
  split,
  split; dec_trivial,
  sorry -- oops
end

example : game puzzle_1 :=
begin [fifteen_tactic']

end

example : game easy_cheesy :=
begin
  slide_tile dd,
  have H : (slide dd dc easy_cheesy).map = goal_position.map := by exact dec_trivial,
  have H' : (slide dd dc easy_cheesy) = goal_position := by tauto,
  rw H',
  apply can_slide_to.self goal_position,
end

example : game easy_cheesy :=
begin [fifteen_tactic']
  slide_tile dd,
end