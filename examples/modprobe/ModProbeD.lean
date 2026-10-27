module

public import ModProbeA
import all ModProbeA

/-! Probe D: `import all` makes A's private scope visible. -/

example : secretA = 3 := rfl

example : hiddenBody = 3 := rfl
