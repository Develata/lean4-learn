module

/-! Probe A: one hidden-body, one exposed-body and one private definition. -/

public def hiddenBody : Nat := 3

@[expose] public def shownBody : Nat := 3

private def secretA : Nat := 3

public theorem hiddenBody_eq : hiddenBody = 3 := by unfold hiddenBody; rfl
