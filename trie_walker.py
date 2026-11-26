"""Zipper-based finite-control traversal for the published S trie.

The generation identities are Filin (2026), Appendix C.4. This separate
implementation keeps one protected-tree cursor (zipper) and finite control;
it does not store a frontier queue, source-machine state or tree depth.
The zipper is the unbounded cursor/parent context required to navigate a tree.
"""
import json
from trie_generator import Trie


class Walker:
    def __init__(self, trie):
        self.trie = trie
        self.p = trie.p
        self.S = trie.S
        self.root = trie.term
        self.frames = []
        self.contractions = 0
        self.visits = 0
        self.trace = None
        self.ambient = []

    def whole_term(self, focus):
        """Read the immutable whole term represented by this zipper."""
        for side, sibling, junk in reversed(self.frames):
            focus = (self.trie.protected(focus, sibling, junk) if side == 0
                     else self.trie.protected(sibling, focus, junk))
        for side, sibling in reversed(self.ambient):
            focus = (self.p.app(focus, sibling) if side == 0
                     else self.p.app(sibling, focus))
        return focus

    def apply_focus_step(self, focus, address):
        focus = self.step_inside(focus, address)
        if self.trace is not None:
            self.trace.append(self.whole_term(focus))
        return focus

    def step_inside(self, term, address):
        if address:
            l, r = self.p.nodes[term]
            if address[0] == 0:
                return self.p.app(self.step_inside(l, address[1:]), r)
            return self.p.app(l, self.step_inside(r, address[1:]))
        l, z = self.p.nodes[term]
        ll, y = self.p.nodes[l]
        head, x = self.p.nodes[ll]
        assert head == self.S
        self.contractions += 1
        return self.p.app(self.p.app(x, z), self.p.app(y, z))

    def open_focus(self, focus):
        pair = self.p.nodes[focus]
        assert pair is not None and pair[1] == self.S
        inner = self.p.nodes[pair[0]]
        assert inner is not None
        c = inner[0]
        if c == self.trie.c[0]:
            focus = self.apply_focus_step(focus, (0,))
        else:
            node = self.p.nodes[c]
            assert node is not None and node[0] == self.trie.b
        for address in [(0,), (), (0,), (), (1, 0), (1,)]:
            focus = self.apply_focus_step(focus, address)
        assert self.trie.parse_protected(focus) is not None
        return focus

    def round(self):
        # A round opens all the pre-existing protected leaves exactly once.
        # Each zipper frame stores side, sibling and junk from one parent.
        focus = self.root
        self.ambient = []
        for side in self.trie.body_path:
            left, right = self.p.nodes[focus]
            self.ambient.append((side, right if side == 0 else left))
            focus = left if side == 0 else right
        assert not self.frames
        opened = 0
        while True:
            # DOWN: fixed-shape test, descending through the left field.
            while True:
                protected = self.trie.parse_protected(focus)
                if protected is None:
                    break
                left, right, junk = protected
                self.frames.append((0, right, junk))
                focus = left
                self.visits += 1
            focus = self.open_focus(focus)
            opened += 1

            # UP: skip the new children. First left parent offers an
            # unvisited right sibling; a right parent is already finished.
            while self.frames:
                side, sibling, junk = self.frames.pop()
                self.visits += 1
                if side == 0:
                    self.frames.append((1, focus, junk))
                    focus = sibling
                    break
                focus = self.trie.protected(sibling, focus, junk)
            else:
                self.root = self.whole_term(focus)
                return opened


def main():
    # Compare literal resulting trees, not only output counts, against the
    # earlier path-based scheduler on a shared immutable hash-consing pool.
    t = Trie((1, 0, 1, 1))
    t.bootstrap_ten_leaf_seed()
    walker = Walker(t)
    t.trace = []
    walker.trace = []
    rows = []
    for depth in range(8):
        n = walker.round()
        expected = t.round()
        assert n == expected == 2**depth
        assert walker.root == t.term
        assert walker.trace == t.trace
        assert not walker.frames
        rows.append({'depth': depth, 'opened': n})
    print(json.dumps({'rounds': rows, 'literal_tree_agreement': True,
                      'bootstrap_s_leaves': 10,
                      'bootstrap_contractions': 5,
                      'every_contraction_tree_agrees': len(walker.trace),
                      'native_contractions': walker.contractions,
                      'cursor_parent_moves': walker.visits,
                      'dag_nodes': len(t.p.nodes)}, indent=2))


if __name__ == '__main__':
    main()
