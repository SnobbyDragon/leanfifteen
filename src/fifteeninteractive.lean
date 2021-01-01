import fifteenwidget

/-
  Courtesy of Ed Ayers!

  Magic so you can do:
  begin [fifteen_tactic]
  ...
  end
-/

meta def fifteen_tactic := tactic

namespace fifteen_tactic
  open tactic
  local attribute [reducible] fifteen_tactic
  meta instance : monad fifteen_tactic := infer_instance

  meta def step {α : Type} (m : fifteen_tactic α) : fifteen_tactic unit :=
  tactic.step m

  meta def istep {α} (a b c d : ℕ) (t : fifteen_tactic α) : fifteen_tactic unit :=
  tactic.istep a b c d t

  meta def save_info (p : pos) : fifteen_tactic unit := fifteen_save_info p

  meta instance : interactive.executor fifteen_tactic :=
  { config_type := unit,
    execute_with := λ n tac, tac
  }

end fifteen_tactic


-- with clicking
meta def fifteen_tactic' := tactic

namespace fifteen_tactic'
  open tactic
  local attribute [reducible] fifteen_tactic'
  meta instance : monad fifteen_tactic' := infer_instance

  meta def step {α : Type} (m : fifteen_tactic' α) : fifteen_tactic' unit :=
  tactic.step m

  meta def istep {α} (a b c d : ℕ) (t : fifteen_tactic' α) : fifteen_tactic' unit :=
  tactic.istep a b c d t

  meta def save_info (p : pos) : fifteen_tactic' unit := fifteen_save_info' p

  meta instance : interactive.executor fifteen_tactic' :=
  { config_type := unit,
    execute_with := λ n tac, tac
  }

end fifteen_tactic'