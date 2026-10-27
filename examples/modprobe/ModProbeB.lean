module

import ModProbeA

/-! Probe B: plain `import` of A, then a public definition that mentions A's names. -/

public def useShown : Nat := shownBody
