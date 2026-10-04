#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if rg -n '\b(sorry|axiom|admit)\b' --glob '*.lean' NewLang NewLang.lean; then
  echo 'Unexpected proof placeholder or added axiom in project Lean sources.' >&2
  exit 1
else
  status=$?
  if [ "$status" -ne 1 ]; then exit "$status"; fi
fi
lake build
check_file=$(mktemp --suffix=.lean)
trap 'rm -f "$check_file"' EXIT
printf 'import NewLang\n' > "$check_file"
declarations=(
  NewLang.F0.wellFormed_surviving_dependencies_live
  NewLang.F0.empty_wellFormed
  NewLang.F0.replace_preserves_wellFormed
  NewLang.F0.replace_preserves_incarnation
  NewLang.F0.replace_preserves_governingDomain
  NewLang.F0.replace_preserves_place_and_location
  NewLang.F0.replace_preserves_other_locations
  NewLang.F0.replace_preserves_package_data_and_domains
  NewLang.F0.replace_creates_fresh_current_fact
  NewLang.F0.replace_history_monotone
  NewLang.F0.replace_old_fact_remains_used
  NewLang.F0.replace_old_package_survives_as_loose
  NewLang.F0.replace_new_package_installed
  NewLang.F0.rawReplace_old_current_fact_not_live
  NewLang.F0.replace_rejects_surviving_old_current_dependency
  NewLang.F0.replace_rejects_incoming_old_current_dependency
  NewLang.F0.replace_rejects_previously_used_fact
  NewLang.F0.Counterexample.Replace.before_wellFormed
  NewLang.F0.Counterexample.Replace.independent_replace_is_legal
  NewLang.F0.Counterexample.Replace.unchecked_replace_launders_old_dependency
  NewLang.F0.Counterexample.Replace.old_dependency_is_rejected
  NewLang.F0.Counterexample.Replace.incoming_dependency_is_rejected
  NewLang.F0.Counterexample.Replace.currently_dead_is_not_historically_fresh
  NewLang.F0.RawStore.target_after
  NewLang.F0.RawStore.packages_unchanged
  NewLang.F0.RawStore.incoming_ne_old
  NewLang.F0.RawStore.newFact_ne_old
  NewLang.F0.store_history_monotone
  NewLang.F0.store_preserves_wellFormed
  NewLang.F0.store_preserves_incarnation
  NewLang.F0.store_preserves_governingDomain
  NewLang.F0.store_preserves_place_and_location
  NewLang.F0.store_preserves_other_locations
  NewLang.F0.store_preserves_package_data_and_domains
  NewLang.F0.store_creates_fresh_current_fact
  NewLang.F0.store_old_fact_remains_used
  NewLang.F0.store_new_package_installed
  NewLang.F0.rawStore_old_package_does_not_survive
  NewLang.F0.store_old_package_does_not_survive
  NewLang.F0.store_other_survivors_preserved
  NewLang.F0.rawStore_old_current_fact_not_live
  NewLang.F0.store_rejects_other_surviving_old_current_dependency
  NewLang.F0.store_rejects_incoming_old_current_dependency
  NewLang.F0.store_requires_discardable_old_package
  NewLang.F0.store_rejects_nondiscardable_old_package
  NewLang.F0.store_rejects_previously_used_fact
  NewLang.F0.Counterexample.Store.before_wellFormed
  NewLang.F0.Counterexample.Store.store_can_eliminate_old_only_dependency
  NewLang.F0.Counterexample.Store.old_self_dependency_rejects_replace_but_allows_store
  NewLang.F0.Counterexample.Store.old_only_dependency_removed_from_validation
  NewLang.F0.Counterexample.Store.incoming_need_not_be_discardable
  NewLang.F0.Counterexample.Store.other_survivor_dependency_is_rejected
  NewLang.F0.Counterexample.Store.incoming_dependency_is_rejected
  NewLang.F0.Counterexample.Store.nondiscardable_old_package_is_rejected
  NewLang.F0.Counterexample.Store.unchecked_other_dependency_breaks_candidate
  NewLang.F0.Counterexample.Store.unchecked_discardability_silently_loses_package
  NewLang.F0.Counterexample.Store.currently_dead_fact_cannot_be_reused
)
for declaration in "${declarations[@]}"; do
  printf '#print axioms %s\n' "$declaration" >> "$check_file"
done
if proof_output=$(lake env lean "$check_file" 2>&1); then
  :
else
  status=$?
  printf '%s\n' "$proof_output" >&2
  exit "$status"
fi
printf '%s\n' "$proof_output"
report_count=0
report=''
while IFS= read -r line; do
  report="${report:+$report }$line"
  case "$report" in
    *'depends on axioms: ['*)
      # Lean may wrap long theorem reports across several output lines.
      if [[ "$report" != *']' ]]; then continue; fi
      names="${report##*depends on axioms: [}"
      names="${names%]}"
      IFS=', ' read -r -a axiom_names <<< "$names"
      for name in "${axiom_names[@]}"; do
        case "$name" in
          propext|Classical.choice|Quot.sound) ;;
          *) echo "Unexpected proof axiom: $name" >&2; exit 1 ;;
        esac
      done
      ;;
    *'does not depend on any axioms') ;;
    *) echo "Unexpected Lean axiom report: $report" >&2; exit 1 ;;
  esac
  report_count=$((report_count + 1))
  report=''
done <<< "$proof_output"
if [ -n "$report" ] || [ "$report_count" -ne "${#declarations[@]}" ]; then
  echo 'Not all requested theorem axiom reports were produced.' >&2
  exit 1
fi
printf 'Verified %s theorem axiom reports (standard Lean logic only).\n' "$report_count"
