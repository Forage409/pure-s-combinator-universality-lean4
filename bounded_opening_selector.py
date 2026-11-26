"""Bounded-shape selector for one protected-trie opening contraction."""


def arity_at_most_four(pool, term):
    """Return 0..4, or 5 for any larger S-headed application spine."""
    count = 0
    while count < 5 and pool.nodes[term] is not None:
        term = pool.nodes[term][0]
        count += 1
    return count


def bounded_next_address(trie, term):
    if trie.parse_protected(term) is not None:
        return None
    arity = arity_at_most_four(trie.p, term)
    if arity == 4:
        return (0,)
    if arity == 3:
        return ()
    if arity == 2:
        right = trie.p.nodes[term][1]
        right_arity = arity_at_most_four(trie.p, right)
        if right_arity == 4:
            return (1, 0)
        if right_arity == 3:
            return (1,)
    raise ValueError('term is not a recognized intermediate opening state')


def main():
    from trie_generator import Trie
    from stateless_opening import next_address
    from s_engine import enumerate_trees_by_size
    import json
    trie = Trie()
    count = 0
    for term in (root for level in enumerate_trees_by_size(trie.p, 10).values() for root in level):
        outcomes = []
        for rule in (next_address, bounded_next_address):
            try:
                outcomes.append(('return', rule(trie, term)))
            except ValueError:
                outcomes.append(('reject', None))
        assert outcomes[0] == outcomes[1]
        count += 1
    print(json.dumps({'all_ground_terms_max_leaves': 10, 'terms_checked': count,
                      'bounded_and_existing_opening_selector_agree': True,
                      'max_left_spine_edges_inspected': 5}))


if __name__ == '__main__':
    main()

