"""Recover the next native contraction of a protected-trie opening.

This uses only the current focused S term, not the opening phase, m, n, or a
saved cursor. The underlying six/seven-step identities are Filin (2026).
"""
import json
from trie_generator import Trie


def next_address(trie, term):
    p = trie.p
    if trie.parse_protected(term) is not None:
        return None
    spine = p.spine(term)
    if len(spine) == 4:
        return (0,)
    if len(spine) == 3:
        return ()
    if len(spine) == 2:
        right = p.nodes[term][1]
        right_arity = len(p.spine(right))
        if right_arity == 4:
            return (1,0)
        if right_arity == 3:
            return (1,)
    raise ValueError('term is not a recognized intermediate opening state')


def main():
    cases = contractions = 0
    for n in range(2,21):
        for m in range(n+1):
            trie = Trie()
            initial = trie.generator(m,n)
            trie.term = initial
            trie.trace = []
            trie.open_local(())
            expected = list(trie.trace)
            trie.term = initial
            trie.trace = None
            actual = []
            while True:
                address = next_address(trie,trie.term)
                if address is None:
                    break
                trie.contract(address)
                actual.append(trie.term)
            assert actual == expected
            assert len(actual) == (7 if m==0 else 6)
            cases += 1
            contractions += len(actual)
    print(json.dumps({'generator_phases':cases,
                      'individual_contractions':contractions,
                      'all_states_exactly_match_reference':True,
                      'saved_phase_required':False},indent=2))


if __name__=='__main__':
    main()
