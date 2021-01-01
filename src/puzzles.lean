import fifteen

open fifteen fifteen.tile fifteen.position

namespace puzzles

/-
  Not all puzzles are solvable!
  Is there a generator for solvable puzzles?

  Here are some puzzles by hand...
  (https://www.chiark.greenend.org.uk/~sgtatham/puzzles/js/fifteen.html)
-/

def easy_cheesy : position :=
⟨ λ t, match t with
  | aa := 1 | ab := 2 | ac := 3 | ad := 4
  | ba := 5 | bb := 6 | bc := 7 | bd := 8
  | ca := 9 | cb := 10| cc := 11| cd := 12
  | da := 13| db := 14| dc := 0 | dd := 15
  end 
⟩

def puzzle_1 : position :=
⟨ λ t, match t with
  | aa := 5 | ab := 7 | ac := 2 | ad := 11
  | ba := 10| bb := 13| bc := 9 | bd := 0
  | ca := 3 | cb := 14| cc := 12| cd := 15
  | da := 6 | db := 1 | dc := 8 | dd := 4
  end 
⟩

end puzzles