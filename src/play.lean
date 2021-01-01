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
  finish_game,
end

example : game easy_cheesy :=
begin [fifteen_tactic']
  slide_tile dd,
end