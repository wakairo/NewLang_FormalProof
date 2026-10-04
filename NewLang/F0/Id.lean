/-! Nominal proof identities; Nat fields are not NewLang runtime requirements. -/
namespace NewLang.F0

structure PlaceId where
  index : Nat
  deriving DecidableEq, Repr

structure IncarnationId where
  index : Nat
  deriving DecidableEq, Repr

structure ValueFactId where
  index : Nat
  deriving DecidableEq, Repr

structure DomainId where
  index : Nat
  deriving DecidableEq, Repr

structure PackageId where
  index : Nat
  deriving DecidableEq, Repr

structure RootLocationId where
  index : Nat
  deriving DecidableEq, Repr

/-- Abstract owner of a domain value; not a machine address or a package/location ID. -/
structure DomainValueCarrierId where
  index : Nat
  deriving DecidableEq, Repr

end NewLang.F0
