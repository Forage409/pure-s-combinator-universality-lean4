"""Check the published pure-S protected binary-trie generator.

The constructions and local contractions are from Filin (2026), Appendix C.4.
This independent implementation verifies them for finite levels and provides
a basis for experimenting with compact, explicitly bounded observers.
"""
from collections import Counter
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from s_engine import DAGPool


class Trie:
    def __init__(self, header_bits=None):
        self.p = DAGPool()
        self.S = self.p.S
        self.b = self.p.app(self.S, self.S)
        self.c = [self.p.app_many(self.S, [self.b, self.b])]
        self.term = self.generator(2, 2)
        self.body_path = ()
        if header_bits is not None:
            header = self.S
            one_marker = self.p.app(self.S, self.b)
            for bit in reversed(header_bits):
                header = self.p.app(self.b if bit == 0 else one_marker, header)
            self.term = self.p.app_many(self.S, [header, self.term])
            self.body_path = (1,)
        self.steps = 0
        self.trace = None

    def numeral(self, n):
        while len(self.c) <= n:
            self.c.append(self.p.app(self.b, self.c[-1]))
        return self.c[n]

    def generator(self, m, n):
        return self.p.app(self.p.app(self.numeral(m), self.numeral(n)), self.S)

    def protected(self, l, r, j):
        return self.p.app_many(self.S, [l, self.p.app_many(self.S, [r, j])])

    def bootstrap_eleven_leaf_seed(self):
        """Replace the unopened body with D(0,0) and reach D(2,2).

        This uses four actual S contractions. D(0,0) is the seed of the
        published C0 C0 E clock specialized to E=S; no novelty is claimed.
        """
        body = self.body_path
        seed = self.generator(0, 0)
        assert self.p.leaf_count(seed) == 11
        self.term = self.replace(self.term, body, seed)
        for rel in [(0,), (0,), (), (1, 0)]:
            self.contract(body + rel)
        self.body_path = body + (1,)
        assert self.at(self.body_path) == self.generator(2, 2)

    def bootstrap_ten_leaf_seed(self):
        """Start one native S step before D(0,0), then open the clock."""
        body = self.body_path
        sb = self.p.app(self.S, self.b)
        seed = self.p.app(self.p.app_many(self.S, [sb, sb, self.b]), self.S)
        assert self.p.leaf_count(seed) == 10
        self.term = self.replace(self.term, body, seed)
        self.contract(body + (0,))
        assert self.at(body) == self.generator(0, 0)
        for rel in [(0,), (0,), (), (1, 0)]:
            self.contract(body + rel)
        self.body_path = body + (1,)
        assert self.at(self.body_path) == self.generator(2, 2)

    def at(self, path):
        t = self.term
        for side in path:
            t = self.p.nodes[t][side]
        return t

    def replace(self, t, path, value):
        # Rebuild the selected occurrence iteratively: long tape/backbone
        # paths should not depend on Python's recursion limit.
        frames=[]
        for side in path:
            a,b=self.p.nodes[t]
            frames.append((side,b if side==0 else a))
            t=a if side==0 else b
        for side,sibling in reversed(frames):
            value=(self.p.app(value,sibling) if side==0
                   else self.p.app(sibling,value))
        return value

    def contract(self, path):
        t = self.at(path)
        l, z = self.p.nodes[t]
        ll, y = self.p.nodes[l]
        head, x = self.p.nodes[ll]
        assert head == self.S
        self.term = self.replace(self.term, path,
                                 self.p.app(self.p.app(x, z), self.p.app(y, z)))
        self.steps += 1
        if self.trace is not None:
            self.trace.append(self.term)

    def parse_numeral(self, t):
        n = 0
        while t != self.c[0]:
            pair = self.p.nodes[t]
            if pair is None or pair[0] != self.b:
                return None
            n += 1
            t = pair[1]
        return n

    def parse_generator(self, t):
        pair = self.p.nodes[t]
        if pair is None or pair[1] != self.S:
            return None
        inner = self.p.nodes[pair[0]]
        if inner is None:
            return None
        m, n = map(self.parse_numeral, inner)
        if m is None or n is None or n < 2 or m > n:
            return None
        return m, n

    def parse_protected(self, t):
        pair = self.p.nodes[t]
        if pair is None:
            return None
        left, right = pair
        left = self.p.nodes[left]
        right = self.p.nodes[right]
        if left is None or left[0] != self.S or right is None:
            return None
        right_head = self.p.nodes[right[0]]
        if right_head is None or right_head[0] != self.S:
            return None
        return left[1], right_head[1], right[1]

    def open(self, path):
        phase = self.parse_generator(self.at(path))
        assert phase is not None
        m, n = phase
        if m == 0:
            self.contract(path + (0,))
            m, n = n + 1, n + 1
            assert self.parse_generator(self.at(path)) == (m, n)
        for rel in [(0,), (), (0,), (), (1, 0), (1,)]:
            self.contract(path + rel)
        child = self.generator(m - 1, n)
        junk = self.p.app(self.p.app(self.numeral(n - 2), self.S), child)
        assert self.at(path) == self.protected(child, child, junk)

    def open_local(self, path):
        """Open a valid generator using only a constant-depth zero test.

        The six/seven rule positions are fixed. No numerical phase is read or
        computed; the global good-generator invariant justifies the redexes.
        """
        term = self.at(path)
        pair = self.p.nodes[term]
        assert pair is not None and pair[1] == self.S
        inner = self.p.nodes[pair[0]]
        assert inner is not None
        first = inner[0]
        if first == self.c[0]:
            self.contract(path + (0,))
        else:
            succ = self.p.nodes[first]
            assert succ is not None and succ[0] == self.b
        for rel in [(0,), (), (0,), (), (1, 0), (1,)]:
            self.contract(path + rel)
        assert self.parse_protected(self.at(path)) is not None

    @staticmethod
    def child_path(path, bit):
        return path + ((0, 1) if bit == 0 else (1, 0, 1))

    def descend(self, path):
        """Descend to first unopened protected field, always taking left."""
        while self.parse_generator(self.at(path)) is None:
            assert self.parse_protected(self.at(path)) is not None
            path = self.child_path(path, 0)
        return path

    @staticmethod
    def after_address(bits):
        """Next sibling after skipping this newly opened subtree."""
        i = len(bits) - 1
        while i >= 0 and bits[i] == 1:
            i -= 1
        return None if i < 0 else bits[:i] + (1,)

    def round(self):
        # Traversal state is one cursor address; no source computation occurs.
        bits = ()
        count = 0
        while bits is not None:
            path = self.body_path
            for bit in bits:
                assert self.parse_protected(self.at(path)) is not None
                path = self.child_path(path, bit)
            while self.parse_generator(self.at(path)) is None:
                assert self.parse_protected(self.at(path)) is not None
                bits += (0,)
                path = self.child_path(path, 0)
            self.open_local(path)
            count += 1
            bits = self.after_address(bits)
        return count

    def opened_paths(self):
        result = []
        def walk(path, bits):
            if self.parse_protected(self.at(path)) is None:
                return
            result.append(bits)
            walk(self.child_path(path, 0), bits + (0,))
            walk(self.child_path(path, 1), bits + (1,))
        walk(self.body_path, ())
        return result


def main():
    # Compare the local finite-control implementation with the independently
    # computed phase/formula implementation on every small valid phase.
    phase_checks = 0
    for n in range(2, 11):
        for m in range(n + 1):
            verifier = Trie()
            initial = verifier.generator(m, n)
            verifier.term = initial
            verifier.open(())
            expected = verifier.term
            verifier.term = initial
            verifier.open_local(())
            assert verifier.term == expected
            phase_checks += 1
    t = Trie()
    rows = []
    for level in range(5):
        before = t.steps
        count = t.round()
        paths = t.opened_paths()
        counts = Counter(map(len, paths))
        assert count == 2**level
        assert len(paths) == 2**(level+1)-1
        assert all(counts[d] == 2**d for d in range(level+1))
        rows.append({'level': level, 'opened': count,
                     'native_contractions': t.steps-before,
                     'total_opened': len(paths),
                     'dag_nodes': len(t.p.nodes)})
    print(json.dumps({'phase_checks': phase_checks, 'rounds': rows,
                      'total_contractions': t.steps}, indent=2))


if __name__ == '__main__':
    main()
