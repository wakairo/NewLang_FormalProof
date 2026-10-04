# F0.0 formalization notes

[日本語](FORMALIZATION_NOTES.ja.md)

The supplied specifications are preserved unchanged. Draft 17.4 remains the normative source of truth.

- **FORMAL-ENCODING**: The reference shape `RootLocationId → Occupancy` can represent two locations with the same PlaceId and different current facts. `PlacesUnique` excludes this malformed state and implements WF-4. Carriers distinguish locations so duplicate installation of the same package cannot be hidden by duplicate place identities. This is an encoding constraint, not a change to normative semantics.
- **FORMAL-ENCODING**: The optional identification of PlaceId and RootLocationId in F0 §4.2 is not used. They remain nominally distinct. Predicates establish their one-to-one correspondence for well-formed live roots and the uniqueness of a live root's incarnation identity.
- **FORMAL-SCOPE**: F0 §20.2/20.3 calls domain transfer/finalization “F0.2”, while the proof sequence in §28 uses F0.2 for store. This milestone-number inconsistency does not affect F0.0 semantics. The next milestone follows the requested F0.1 replace and §28. The supplied bridge document is not edited.
- **FORMAL-SCOPE**: Finite support, historical freshness, authorization, payload, authority conservation, structural places, scope/backing facts, and transitions are not verified here. State the necessary premises and invariants when extending the model. In particular, do not equate “currently unused” with “historically fresh”.

No FORMAL-HOLE or FORMAL-AMBIGUITY was identified in the related sections inspected for F0.0. This does not establish the soundness of the entire specification.
