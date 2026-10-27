module

/-! Probe E: a public theorem whose proof needs to unfold a definition that is not exposed. -/

public def hiddenBody : Nat := 3

public theorem hiddenBody_eq : hiddenBody = 3 := rfl
