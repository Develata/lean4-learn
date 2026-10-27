module

import ModProbeA

/-! Probe F: plain `import` of A; every example below is tried with the default settings. -/

example : shownBody = 3 := rfl

example : hiddenBody = 3 := rfl

example : hiddenBody = 3 := by simp [hiddenBody]

example : hiddenBody = 3 := by unfold hiddenBody; rfl

example : hiddenBody = 3 := hiddenBody_eq

example : secretA = 3 := rfl
