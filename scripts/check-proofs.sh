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
  NewLang.F0.swap_same_is_identity
  NewLang.F0.swap_same_preserves_history
  NewLang.F0.swap_same_preserves_current_fact
  NewLang.F0.swap_same_preserves_package
  NewLang.F0.same_swap_is_legal
  NewLang.F0.RawSwapDistinct.targets_after
  NewLang.F0.RawSwapDistinct.packages_distinct
  NewLang.F0.RawSwapDistinct.places_distinct
  NewLang.F0.swap_distinct_preserves_wellFormed
  NewLang.F0.swap_distinct_preserves_incarnations
  NewLang.F0.swap_distinct_preserves_governingDomains
  NewLang.F0.swap_distinct_preserves_places_and_locations
  NewLang.F0.swap_distinct_exchanges_packages
  NewLang.F0.swap_distinct_both_packages_survive
  NewLang.F0.swap_distinct_preserves_loose_packages
  NewLang.F0.swap_distinct_preserves_package_data_and_domains
  NewLang.F0.swap_distinct_preserves_other_locations
  NewLang.F0.swap_distinct_history_monotone
  NewLang.F0.swap_distinct_creates_two_fresh_current_facts
  NewLang.F0.swap_distinct_old_facts_remain_used
  NewLang.F0.swap_distinct_survivors_preserved
  NewLang.F0.rawSwapDistinct_old_left_fact_not_live
  NewLang.F0.rawSwapDistinct_old_right_fact_not_live
  NewLang.F0.swap_rejects_surviving_old_current_dependency
  NewLang.F0.swap_rejects_left_self_current_dependency
  NewLang.F0.swap_rejects_left_package_cross_dependency
  NewLang.F0.swap_rejects_right_self_current_dependency
  NewLang.F0.swap_rejects_right_package_cross_dependency
  NewLang.F0.swap_rejects_reused_left_fact
  NewLang.F0.swap_rejects_reused_right_fact
  NewLang.F0.swap_rejects_colliding_new_facts
  NewLang.F0.Counterexample.Swap.before_wellFormed
  NewLang.F0.Counterexample.Swap.independent_distinct_swap_is_legal
  NewLang.F0.Counterexample.Swap.swap_does_not_require_discardable
  NewLang.F0.Counterexample.Swap.same_place_swap_preserves_self_dependency
  NewLang.F0.Counterexample.Swap.left_self_dependency_is_rejected
  NewLang.F0.Counterexample.Swap.right_self_dependency_is_rejected
  NewLang.F0.Counterexample.Swap.left_cross_dependency_is_rejected
  NewLang.F0.Counterexample.Swap.right_cross_dependency_is_rejected
  NewLang.F0.Counterexample.Swap.self_dependency_allows_same_swap_but_rejects_distinct_swap
  NewLang.F0.Counterexample.Swap.swap_rejects_cyclic_dependency_laundering
  NewLang.F0.Counterexample.Swap.third_survivor_left_dependency_is_rejected
  NewLang.F0.Counterexample.Swap.third_survivor_right_dependency_is_rejected
  NewLang.F0.Counterexample.Swap.unchecked_cyclic_swap_breaks_dependencies
  NewLang.F0.Counterexample.Swap.historical_reuse_and_pair_collision_are_rejected
  NewLang.F0.replace_preserves_incarnation_history
  NewLang.F0.store_preserves_incarnation_history
  NewLang.F0.swap_same_preserves_incarnation_history
  NewLang.F0.swap_distinct_preserves_incarnation_history
  NewLang.F0.RawInitialize.target_after
  NewLang.F0.initialize_preserves_wellFormed
  NewLang.F0.initialize_consumes_vacancy
  NewLang.F0.initialize_installs_package
  NewLang.F0.initialize_package_unique_installed_carrier
  NewLang.F0.initialize_incarnation_history_monotone
  NewLang.F0.initialize_value_fact_history_monotone
  NewLang.F0.initialize_creates_fresh_incarnation
  NewLang.F0.initialize_creates_fresh_current_fact
  NewLang.F0.initialize_creates_governing_relation
  NewLang.F0.initialize_uses_stable_site_place
  NewLang.F0.initialize_preserves_other_locations
  NewLang.F0.initialize_preserves_package_data
  NewLang.F0.initialize_preserves_live_domains
  NewLang.F0.initialize_rejects_reused_incarnation
  NewLang.F0.initialize_rejects_reused_current_fact
  NewLang.F0.initialize_rejects_dead_domain
  NewLang.F0.initialize_rejects_missing_authority
  NewLang.F0.take_preserves_wellFormed
  NewLang.F0.take_restores_vacancy
  NewLang.F0.take_preserves_other_locations
  NewLang.F0.take_preserves_package_data
  NewLang.F0.take_preserves_live_domains
  NewLang.F0.take_preserves_identity_histories
  NewLang.F0.take_ended_identities_remain_recorded
  NewLang.F0.take_ends_incarnation
  NewLang.F0.take_old_current_fact_not_live
  NewLang.F0.take_ends_governing_relation
  NewLang.F0.take_does_not_finalize_domain
  NewLang.F0.take_rejects_wrong_ending_domain
  NewLang.F0.take_rejects_missing_authority
  NewLang.F0.destroy_preserves_wellFormed
  NewLang.F0.destroy_restores_vacancy
  NewLang.F0.destroy_preserves_other_locations
  NewLang.F0.destroy_preserves_package_data
  NewLang.F0.destroy_preserves_live_domains
  NewLang.F0.destroy_preserves_identity_histories
  NewLang.F0.destroy_ended_identities_remain_recorded
  NewLang.F0.destroy_ends_incarnation
  NewLang.F0.destroy_old_current_fact_not_live
  NewLang.F0.destroy_ends_governing_relation
  NewLang.F0.destroy_does_not_finalize_domain
  NewLang.F0.destroy_rejects_wrong_ending_domain
  NewLang.F0.destroy_rejects_missing_authority
  NewLang.F0.take_old_package_survives_as_loose
  NewLang.F0.take_old_package_unique_loose_carrier
  NewLang.F0.take_survivors_preserved
  NewLang.F0.take_rejects_surviving_old_current_dependency
  NewLang.F0.take_rejects_old_self_current_dependency
  NewLang.F0.destroy_old_package_does_not_survive
  NewLang.F0.destroy_other_survivors_preserved
  NewLang.F0.destroy_rejects_other_surviving_old_current_dependency
  NewLang.F0.destroy_requires_discardable_old_package
  NewLang.F0.destroy_rejects_nondiscardable_old_package
  NewLang.F0.Counterexample.Lifetime.before_wellFormed
  NewLang.F0.Counterexample.Lifetime.independent_take_is_legal
  NewLang.F0.Counterexample.Lifetime.take_accepts_nondiscardable_value
  NewLang.F0.Counterexample.Lifetime.take_preserves_domain_live_dependency
  NewLang.F0.Counterexample.Lifetime.independent_destroy_is_legal
  NewLang.F0.Counterexample.Lifetime.destroy_can_eliminate_old_only_dependency
  NewLang.F0.Counterexample.Lifetime.old_self_dependency_rejects_take_but_allows_destroy
  NewLang.F0.Counterexample.Lifetime.third_survivor_rejects_take
  NewLang.F0.Counterexample.Lifetime.third_survivor_rejects_destroy
  NewLang.F0.Counterexample.Lifetime.nondiscardable_destroy_is_rejected
  NewLang.F0.Counterexample.Lifetime.unchecked_destroy_without_discardability_loses_nondiscardable_package
  NewLang.F0.Counterexample.Lifetime.unchecked_take_breaks_dependencies
  NewLang.F0.Counterexample.Lifetime.unchecked_destroy_third_dependency_breaks_candidate
  NewLang.F0.Counterexample.Lifetime.initialize_accepts_nondiscardable_value
  NewLang.F0.Counterexample.Lifetime.initialize_then_take_conserves_occupancy_responsibility
  NewLang.F0.Counterexample.Lifetime.reinitialize_same_location_uses_fresh_incarnation
  NewLang.F0.Counterexample.Lifetime.dead_historical_incarnation_cannot_be_reused
  NewLang.F0.Counterexample.Lifetime.historical_value_fact_reuse_is_rejected
  NewLang.F0.Counterexample.Lifetime.wrong_domain_and_missing_authority_are_rejected
  NewLang.F0.Counterexample.Lifetime.dead_domain_and_missing_initialize_authority_are_rejected
  NewLang.F0.acquire_ref_targets_exact_location_incarnation
  NewLang.F0.acquire_ref_implies_live_incarnation
  NewLang.F0.acquire_ref_matches_governing_domain
  NewLang.F0.acquire_ref_implies_governing_relation
  NewLang.F0.acquire_ref_implies_live_domain
  NewLang.F0.acquire_ref_rejects_missing_stability_evidence
  NewLang.F0.acquire_ref_rejects_missing_access_or_provenance_premise
  NewLang.F0.acquire_ref_rejects_wrong_domain
  NewLang.F0.acquire_ref_rejects_incarnation_mismatch
  NewLang.F0.ended_incarnation_cannot_acquire_ref
  NewLang.F0.initialize_yields_current_ptr
  NewLang.F0.initialize_ptr_can_acquire_ref
  NewLang.F0.reinitialize_does_not_revive_old_ptr
  NewLang.F0.stale_ptr_after_take_cannot_acquire_ref
  NewLang.F0.stale_ptr_after_destroy_cannot_acquire_ref
  NewLang.F0.take_then_reinitialize_does_not_revive_old_ptr
  NewLang.F0.destroy_then_reinitialize_does_not_revive_old_ptr
  NewLang.F0.ptr_remains_live_across_current_value_replace
  NewLang.F0.Counterexample.Reference.initialized_ptr_is_safely_issued_and_acquires_ref
  NewLang.F0.Counterexample.Reference.take_stale_ptr_contrast
  NewLang.F0.Counterexample.Reference.destroy_stale_ptr_contrast
  NewLang.F0.Counterexample.Reference.same_site_reinitialize_old_ptr_rejected_new_ptr_accepted
  NewLang.F0.Counterexample.Reference.same_site_destroy_reinitialize_old_ptr_rejected_new_ptr_accepted
  NewLang.F0.Counterexample.Reference.missing_stability_wrong_domain_and_missing_access_are_rejected
  NewLang.F0.Counterexample.Reference.replace_changes_current_fact_but_same_ptr_acquires_ref
  NewLang.F0.Counterexample.Reference.omitting_only_incarnation_freshness_revives_stale_ptr
  NewLang.F0.Counterexample.Reference.omitting_incarnation_match_accepts_old_ptr_after_fresh_reinitialize
  NewLang.F0.Counterexample.Reference.omitting_domain_match_accepts_wrong_live_domain
  NewLang.F0.Counterexample.Domain.simple_domain_transfer_is_legal
  NewLang.F0.Counterexample.Domain.governed_root_allows_transfer_but_rejects_finalization
  NewLang.F0.Counterexample.Domain.DomainLive_dependency_allows_transfer_but_rejects_finalization
  NewLang.F0.Counterexample.Domain.independent_domain_finalization_is_legal
  NewLang.F0.Counterexample.Domain.one_carrier_may_hold_multiple_domain_identities
  NewLang.F0.Counterexample.Domain.transfer_with_root_and_dependency_preserves_acquisition
  NewLang.F0.Counterexample.Domain.unchecked_finalization_strands_governed_root_only
  NewLang.F0.Counterexample.Domain.unchecked_finalization_strands_domain_dependency_only
  NewLang.F0.Counterexample.Domain.ending_root_allows_later_domain_finalization
  NewLang.F0.Counterexample.Domain.broken_identity_rename_can_preserve_wellFormed
  NewLang.F0.Counterexample.Domain.missing_permissions_and_wrong_carriers_are_rejected
  NewLang.F0.Counterexample.Domain.dead_domain_cannot_transfer_or_be_finalized_again
  NewLang.F0.domain_transfer_preserves_wellFormed
  NewLang.F0.domain_transfer_preserves_identity
  NewLang.F0.domain_transfer_preserves_liveness
  NewLang.F0.domain_transfer_moves_value_carrier
  NewLang.F0.domain_transfer_preserves_other_carriers
  NewLang.F0.domain_transfer_preserves_roots
  NewLang.F0.domain_transfer_preserves_governing_relations
  NewLang.F0.domain_transfer_preserves_packages
  NewLang.F0.domain_transfer_preserves_histories
  NewLang.F0.domain_transfer_preserves_liveFacts
  NewLang.F0.domain_transfer_preserves_survivors
  NewLang.F0.domain_transfer_preserves_DomainLive_dependencies
  NewLang.F0.raw_domain_transfer_preserves_wellFormed
  NewLang.F0.domain_transfer_step_of_raw
  NewLang.F0.domain_transfer_preserves_acquire_ref
  NewLang.F0.domain_transfer_rejects_missing_permission
  NewLang.F0.domain_transfer_rejects_dead_domain
  NewLang.F0.domain_transfer_rejects_wrong_carrier
  NewLang.F0.finalize_domain_preserves_wellFormed
  NewLang.F0.finalize_domain_ends_identity
  NewLang.F0.finalize_domain_consumes_value_carrier
  NewLang.F0.finalize_domain_preserves_other_domains
  NewLang.F0.finalize_domain_liveDomains_subset
  NewLang.F0.finalize_domain_preserves_other_carriers
  NewLang.F0.finalize_domain_preserves_occupancy
  NewLang.F0.finalize_domain_preserves_packages
  NewLang.F0.finalize_domain_preserves_histories
  NewLang.F0.finalize_domain_preserves_survivors
  NewLang.F0.finalize_domain_preserves_carrier_coherence
  NewLang.F0.finalize_domain_requires_no_governed_roots
  NewLang.F0.finalize_domain_rejects_live_governed_root
  NewLang.F0.finalize_domain_requires_no_surviving_domain_dependency
  NewLang.F0.finalize_domain_rejects_surviving_domain_dependency
  NewLang.F0.finalize_domain_rejects_dead_domain
  NewLang.F0.finalize_domain_rejects_missing_permission
  NewLang.F0.finalize_domain_rejects_wrong_carrier
  NewLang.F0.finalized_domain_cannot_acquire_ref
  NewLang.F0.initialize_preserves_domain_carriers
  NewLang.F0.take_preserves_domain_carriers
  NewLang.F0.destroy_preserves_domain_carriers
  NewLang.F0.replace_preserves_domain_carriers
  NewLang.F0.store_preserves_domain_carriers
  NewLang.F0.swap_same_preserves_domain_carriers
  NewLang.F0.swap_distinct_preserves_domain_carriers
  NewLang.F0.wellFormed_live_domain_has_value_carrier
  NewLang.F0.wellFormed_domain_carrier_implies_live_domain
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
