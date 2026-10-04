import NewLang.F0.Id

namespace NewLang.F0

/-- F0.0 dependency atoms; scope, occurrence and backing facts are out of scope. -/
inductive Fact where
  | valueFact (place : PlaceId) (currentFact : ValueFactId)
  | domainLive (domain : DomainId)
  deriving DecidableEq, Repr

end NewLang.F0
