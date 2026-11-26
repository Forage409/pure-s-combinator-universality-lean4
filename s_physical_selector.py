"""Read-only physical-tree walker for the protected-tape selector.

Unlike the zipper implementation, this walker keeps no protected-parent
frames or sibling/junk references. The cursor path is only its position in
the S occurrence tree. A bounded shape test determines which protected edge
was used when ascending. Native mutation is always performed separately.
"""
import json
from itertools import product
from s_boundary_reset import BoundaryMachine
from s_finite_selector import Selector, select_address
from s_monotone_tape import Instruction
from bounded_opening_selector import bounded_next_address


class FrameView:
    def __init__(self, selector): self.selector = selector
    def __bool__(self): return len(self.selector.path) != len(self.selector.trie.body_path)
    def __getitem__(self, index):
        assert index == -1 and self
        return (self.selector.parent_side(),)


class PhysicalSelector(Selector):
    def __init__(self, program, trie):
        self.program = dict(program)
        states = [0]
        for (state, _), instruction in self.program.items():
            states.extend((state, instruction.next_state))
        self.width = max(1, max(states).bit_length())
        self.trie = trie
        self.path = list(trie.body_path)
        # Cache the physical ancestor nodes of the cursor. This is an
        # implementation of parent pointers, not protected-record metadata.
        self.cursor_nodes = [trie.term]
        for edge in self.path:
            self.cursor_nodes.append(trie.p.nodes[self.cursor_nodes[-1]][edge])
        self.walker = type('Cursor', (), {})()
        self.walker.frames = FrameView(self)
        assert self.opened()

    @property
    def focus(self): return self.cursor_nodes[-1]

    def down(self, side):
        assert self.opened() and side in (0, 1)
        edges = (0, 1) if side == 0 else (1, 0, 1)
        for edge in edges:
            self.cursor_nodes.append(self.trie.p.nodes[self.cursor_nodes[-1]][edge])
        self.path.extend(edges)

    def parent_side(self):
        """Distinguish the two physical edges using constant-depth shape."""
        assert len(self.path) != len(self.trie.body_path)
        assert self.path[-2:] == [0, 1]
        if self.trie.parse_protected(self.cursor_nodes[-3]) is not None:
            return 0
        assert len(self.path) >= len(self.trie.body_path) + 3
        assert self.path[-3:] == [1, 0, 1]
        assert self.trie.parse_protected(self.cursor_nodes[-4]) is not None
        return 1

    def up(self):
        side = self.parent_side()
        distance = 2 if side == 0 else 3
        del self.path[-distance:]
        del self.cursor_nodes[-distance:]

    def to_hub(self):
        while len(self.path) != len(self.trie.body_path):
            self.up()

    def one_native(self):
        address = bounded_next_address(self.trie, self.focus)
        assert address is not None
        return tuple(self.path) + address


def select_physical(program, runner):
    selector = PhysicalSelector(program, runner.trie)
    address = selector.advance()
    return ('halt', None) if address is None else ('step', address)


def main():
    choices = [None] + [Instruction(0, bit, move)
                        for bit in (0, 1) for move in (-1, 0, 1)]
    cases = steps = 0
    for transitions in product(choices, repeat=2):
        program = {(0, bit): rule for bit, rule in enumerate(transitions)
                   if rule is not None}
        for word in ((), (0,), (1,)):
            runner = BoundaryMachine(program, word)
            for _ in range(160):
                before = runner.trie.term
                nodecount = len(runner.trie.p.nodes)
                actual = select_physical(program, runner)
                assert runner.trie.term == before
                assert len(runner.trie.p.nodes) == nodecount
                expected = select_address(program, runner.trie.p, before)
                assert actual == expected, (program, word, actual, expected)
                if actual[0] == 'halt': break
                runner.trie.contract(actual[1])
                steps += 1
            cases += 1
    print(json.dumps({'one_state_program_input_cases': cases,
                      'native_redex_choices_compared': steps,
                      'read_only_occurrence_cursor_agrees': True,
                      'stored_protected_parent_frames': False}, indent=2))


if __name__ == '__main__':
    main()

