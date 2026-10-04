import NewLang.F0.Fact
import Mathlib.Data.Finset.Basic

namespace NewLang.F0

/-- F0 bridge §6: payload and authority algebra are intentionally omitted. -/
structure ValuePackage where
  dependencies : Finset Fact
  discardable : Bool

end NewLang.F0
