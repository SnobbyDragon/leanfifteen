import fifteen

open fifteen fifteen.tile fifteen.position

namespace puzzles

/-
  Not all puzzles are solvable!
  Is there a generator for solvable puzzles?

  Here are some puzzles by hand...
  (https://www.chiark.greenend.org.uk/~sgtatham/puzzles/js/fifteen.html)
-/

def puzzle_1 : position :=
⟨ λ t, match t with
  | aa := 5 | ab := 7 | ac := 2 | ad := 11
  | ba := 10| bb := 13| bc := 9 | bd := 0
  | ca := 3 | cb := 14| cc := 12| cd := 15
  | da := 6 | db := 1 | dc := 8 | dd := 4
  end 
⟩

end puzzles