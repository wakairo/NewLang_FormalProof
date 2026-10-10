/* F51 independent observational probe of frozen production code, NOT a Lean
 * refinement or a Compiler change. The immediate-grant and malformed-owned
 * controls invoke private C primitives; only inspect_source starts from actual
 * NewLang source. No host allocation is promoted to native NewLang authority. */
#include "semantic_internal.h"
#include "node_checked.h"
#include "raw_storage_check.h"

static bool source_seen;
static bool inspect_source(const NLCheckedFragment *f)
{
    const NLSemanticContext *c = nl_checked_context(f);
    CHECK(nl_sem_validate(c) == NL_CHECK_OK && nl_raw_validate(c) == NL_CHECK_OK);
    for (NLCheckedNodeId i = 1; i <= nl_checked_node_count(f); ++i) {
        const NLCheckedNodeView *op = nl_checked_node_view(f, i);
        if (op->kind == NL_CHECKED_TRY_ALLOCATE_ONE &&
            op->result_count == 1 && op->allocation_success) {
            CHECK(!source_seen && op->allocation_size == 24);
            const NLSemanticValueView a = c->values[op->allocation_authority - 1];
            const NLSemanticValueView raw = c->values[op->storage_authority - 1];
            CHECK(a.allocation_region == op->backing && raw.occupancy.region == op->backing);
            CHECK(raw.occupancy.start == 0 && raw.occupancy.length == op->allocation_size);
            CHECK(a.carrier == NL_CARRIER_ENDED && raw.carrier == NL_CARRIER_ENDED);
            CHECK(!c->regions[op->backing - 1].view.live);
            size_t starts = 0, ends = 0, frees = 0;
            const NLCheckedNodeView *start = NULL;
            for (NLCheckedNodeId j = 1; j <= nl_checked_node_count(f); ++j) {
                const NLCheckedNodeView *v = nl_checked_node_view(f, j);
                if (v->kind == NL_CHECKED_INITIALIZE) {
                    start = v;
                    ++starts;
                    CHECK(v->backing == op->backing && v->lifetime_domain != 0);
                    CHECK(v->lifetime_range.start == 0 && v->lifetime_range.length == 24);
                }
                if (v->kind == NL_CHECKED_DESTROY) {
                    ++ends;
                    CHECK(start != NULL && v->lifetime_place == start->lifetime_place);
                    CHECK(v->lifetime_incarnation == start->lifetime_incarnation);
                    CHECK(v->lifetime_domain == start->lifetime_domain);
                    CHECK(v->lifetime_range.region == op->backing);
                }
                if (v->kind == NL_CHECKED_DEALLOCATE) {
                    ++frees;
                    CHECK(ends == 1);
                }
            }
            CHECK(starts == 1 && ends == 1 && frees == 1);
            source_seen = true;
        }
        const NLCheckedFragment *body = nl_checked_call_body(f, i);
        if (body != NULL)
            CHECK(inspect_source(body));
        if (op->kind == NL_CHECKED_MATCH)
            for (size_t arm = 0; arm < op->item_count; ++arm) {
                const NLCheckedFragment *child = nl_checked_match_arm(f, i, arm);
                if (child != NULL)
                    CHECK(inspect_source(child));
            }
    }
    return true;
}

static bool issuer_controls(const char *path, size_t expected_size)
{
    /* Register the real source type/body without executing main. Registry
     * supplies a private target layout, but no allocation/root/domain facts. */
    NLSource *source = NULL;
    NLParser *parser = NULL;
    NLSyntaxTree *tree = NULL;
    NLSemanticContext *c = NULL;
    CHECK(nl_source_load(path, &source) == NL_SOURCE_OK);
    CHECK(nl_parser_create(source, &parser) == NL_PARSE_OK);
    CHECK(nl_parser_parse_function_unit(parser, &tree, NULL) == NL_PARSE_OK);
    CHECK(nl_semantic_create(&c) == NL_CHECK_OK);
    const NLSyntaxTree *units[] = {tree};
    CHECK(nl_semantic_register_function_unit(c, units, 1, NULL) == NL_CHECK_OK);
    NLTypeId h = 0, option = 0;
    for (size_t i = 0; i < c->type_count; ++i)
        if (c->types[i].name != NULL && strcmp(c->types[i].name, "Node") == 0)
            h = i + 1;
    CHECK(h != 0 && nl_allocated_registry(c, h, &option) == NL_CHECK_OK);
    CHECK(c->types[h - 1].view.size == expected_size);
    CHECK(c->region_count == 0 && c->domain_count == 0 && c->value_count == 0);
    NLCheckedNodeView none = {0}, some = {0};
    CHECK(nl_allocated_grant(c, option, false, &none, NULL) == NL_CHECK_OK);
    CHECK(c->region_count == 0 && none.allocation_authority == 0 && none.storage_authority == 0);
    CHECK(nl_allocated_grant(c, option, true, &some, NULL) == NL_CHECK_OK);
    CHECK(c->region_count == 1 && c->domain_count == 0 && c->place_count == 0);
    NLValueId a = some.allocation_authority, s = some.storage_authority;
    NLValueId sum = some.results[0].value, bundle = c->values[sum - 1].sum_payload;
    CHECK(c->values[a - 1].allocation_region == some.backing);
    CHECK(c->values[s - 1].occupancy.region == some.backing);
    CHECK(c->values[s - 1].occupancy.start == 0 && c->values[s - 1].occupancy.length == expected_size);
    CHECK(c->values[bundle - 1].fields[0] == a && c->values[bundle - 1].fields[1] == s);
    CHECK(c->values[a - 1].carrier == NL_CARRIER_AGGREGATE && c->values[a - 1].aggregate_owner == bundle);
    CHECK(c->values[s - 1].carrier == NL_CARRIER_AGGREGATE && c->values[s - 1].aggregate_owner == bundle);
    CHECK(c->values[bundle - 1].carrier == NL_CARRIER_SUM && c->values[bundle - 1].sum_owner == sum);
    CHECK(!c->types[c->values[a - 1].type - 1].view.is_copy);
    CHECK(!c->types[c->values[s - 1].type - 1].view.is_copy);
    CHECK(!c->types[c->values[a - 1].type - 1].view.is_discardable);
    CHECK(!c->types[c->values[s - 1].type - 1].view.is_discardable);
    CHECK(nl_sem_validate(c) == NL_CHECK_OK && nl_raw_validate(c) == NL_CHECK_OK);
    NLSemanticContext *bad = NULL;
    NLValueId duplicate = 0;
    CHECK(nl_sem_clone(c, &bad) == NL_CHECK_OK);
    CHECK(nl_sem_new_value(bad, bad->values[a - 1], &duplicate) == NL_CHECK_OK);
    CHECK(nl_raw_validate(bad) == NL_CHECK_INTERNAL_ERROR);
    nl_semantic_destroy(bad);
    CHECK(nl_sem_clone(c, &bad) == NL_CHECK_OK);
    bad->values[a - 1].carrier = NL_CARRIER_ENDED;
    CHECK(nl_raw_validate(bad) == NL_CHECK_INTERNAL_ERROR);
    nl_semantic_destroy(bad);
    CHECK(nl_sem_clone(c, &bad) == NL_CHECK_OK);
    bad->values[s - 1].occupancy.length = expected_size - 1;
    CHECK(nl_raw_validate(bad) == NL_CHECK_INTERNAL_ERROR);
    nl_semantic_destroy(bad);
    CHECK(nl_sem_clone(c, &bad) == NL_CHECK_OK);
    bad->values[a - 1].aggregate_owner = sum; /* real carrier, wrong owner kind */
    CHECK(nl_raw_validate(bad) == NL_CHECK_OK); /* byte/issuer accounting alone */
    CHECK(nl_sem_validate(bad) == NL_CHECK_INTERNAL_ERROR);
    nl_semantic_destroy(bad);
    nl_semantic_destroy(c);
    nl_syntax_tree_destroy(tree);
    nl_parser_destroy(parser);
    nl_source_destroy(source);
    return true;
}

static bool primitive_controls(void)
{
    /* Controlled raw primitive experiments, not source OneBacking execution. */
    TestSemantic f = {0};
    CHECK(test_semantic_create(&f));
    NLSemanticContext *c = f.context;
    NLSymbolId a, s, other, t, reused, u;
    NLBackingRegionId rb, rc, rd;
    CHECK(raw_allocate(c, 8, 8, true, true, "a", "s", &a, &s, &rb));
    CHECK(raw_allocate(c, 8, 8, true, true, "other", "t", &other, &t, &rc));
    CHECK(rb != rc);
    CHECK(raw_rejected(c, (NLRawOperation){.kind = NL_RAW_DEALLOCATE,
        .operands = {raw_binding(other),raw_binding(s)}},
        NL_CHECK_SEMANTIC_ERROR, "P4-ALLOCATION-MISMATCH"));
    NLCheckedNodeView parts, merged;
    CHECK(raw_run(c, (NLRawOperation){.kind = NL_RAW_SPLIT,
        .operands = {raw_binding(s)}, .data.split_at = {true,7}}, &parts));
    CHECK(nl_raw_validate(c) == NL_CHECK_OK);
    CHECK(raw_rejected(c, (NLRawOperation){.kind = NL_RAW_DEALLOCATE,
        .operands = {raw_binding(a),raw_loose(parts.results[0].value)}},
        NL_CHECK_SEMANTIC_ERROR, "P4-FULL-RANGE-REQUIRED"));
    CHECK(raw_run(c, (NLRawOperation){.kind = NL_RAW_MERGE,
        .operands = {raw_loose(parts.results[0].value),raw_loose(parts.results[1].value)}}, &merged));
    CHECK(raw_run(c, (NLRawOperation){.kind = NL_RAW_DEALLOCATE,
        .operands = {raw_binding(a),raw_loose(merged.results[0].value)}}, NULL));
    CHECK(raw_allocate(c, 8, 8, true, true, "reused", "u", &reused, &u, &rd));
    CHECK(rd != rb && c->regions[rb - 1].view.address == c->regions[rd - 1].view.address);
    CHECK(raw_run(c, (NLRawOperation){.kind = NL_RAW_DEALLOCATE,
        .operands = {raw_binding(other),raw_binding(t)}}, NULL));
    CHECK(raw_run(c, (NLRawOperation){.kind = NL_RAW_DEALLOCATE,
        .operands = {raw_binding(reused),raw_binding(u)}}, NULL));
    CHECK(nl_raw_validate(c) == NL_CHECK_OK);
    nl_semantic_destroy(c);
    return true;
}

int main(int argc, char **argv)
{
    if (argc != 3)
        return 2;
    TestNode source = {0};
    if (!node_checked_load(argv[1], &source) || !inspect_source(source.entry) ||
        !source_seen || !issuer_controls(argv[1], 24) ||
        !issuer_controls(argv[2], 56) || !primitive_controls())
        return 1;
    node_checked_destroy(&source);
    puts("{\"source_single_original_lifecycle\":true,\"immediate_production_issuer\":true,"
         "\"actual_P278_Node_registered_56_byte_grant\":true,"
         "\"none_no_backing_grant\":true,\"same_region_full_raw\":true,"
         "\"actual_nested_carriers\":true,\"duplicate_allocation_poison_rejected\":true,"
         "\"lost_allocation_poison_rejected\":true,\"last_byte_gap_poison_rejected\":true,"
         "\"wrong_aggregate_carrier_poison_rejected\":true,\"wrong_allocation_use_rejected\":true,"
         "\"partial_raw_release_rejected\":true,\"reused_address_distinct_region\":true}");
    return 0;
}
