"""Protected-S tape with finite control and one persistent zipper cursor.

The protected trie and its local 6/7-step opening are due to Filin (2026).
This candidate connects that primitive to an append-only versioned tape.
The controller has finitely many states for any fixed machine; its only
unbounded working location is the cursor/parent context of the S term.
"""
from hashlib import sha256
from itertools import product
import json
import random
from s_monotone_tape import Instruction, STapeMachine, reference as reference_turing
from trie_generator import Trie
from trie_walker import Walker


class CursorMachine:
    def __init__(self, program, input_word):
        self.program = program
        self.trie = Trie()
        self.trie.bootstrap_ten_leaf_seed()
        self.walker = Walker(self.trie)
        self.focus = self.walker.root
        self.walker.ambient = []
        for side in self.trie.body_path:
            left, right = self.trie.p.nodes[self.focus]
            self.walker.ambient.append((side, right if side == 0 else left))
            self.focus = left if side == 0 else right
        self.state = 0
        self.halted = False
        self.source_steps = 0  # diagnostic only

        self.open_here()  # hub: left child is reserved for the halt marker
        self.down(1)
        self.open_here()  # first tape cell
        for i, bit in enumerate(input_word):
            if i:
                self.move_right()
            if bit:
                self.write(1)
        # Return to the first cell using only parent/child moves.
        while self.walker.frames:
            self.up()
        self.down(1)
        self.initial_contractions = self.total_contractions()

    def is_open(self):
        return self.trie.parse_protected(self.focus) is not None

    def open_here(self):
        assert not self.is_open()
        self.focus = self.walker.open_focus(self.focus)

    def down(self, side):
        parts = self.trie.parse_protected(self.focus)
        assert parts is not None
        left, right, junk = parts
        self.walker.frames.append((side, right if side == 0 else left, junk))
        self.focus = left if side == 0 else right

    def up(self):
        side, sibling, junk = self.walker.frames.pop()
        self.focus = (self.trie.protected(self.focus, sibling, junk) if side == 0
                      else self.trie.protected(sibling, self.focus, junk))

    def return_from_version_to_cell(self):
        # Every version is a left child; every tape cell is a right child.
        while self.walker.frames and self.walker.frames[-1][0] == 0:
            self.up()
        assert self.walker.frames and self.walker.frames[-1][0] == 1

    def read(self):
        self.down(0)
        if not self.is_open():
            self.up()
            return 0
        while True:
            self.down(0)
            if not self.is_open():
                self.up()
                break
        self.down(1)
        result = int(self.is_open())
        self.up()
        self.return_from_version_to_cell()
        return result

    def write(self, bit):
        assert bit in (0, 1)
        self.down(0)
        while self.is_open():
            self.down(0)
        self.open_here()
        if bit:
            self.down(1)
            self.open_here()
            self.up()
        self.return_from_version_to_cell()

    def move_right(self):
        self.down(1)
        if not self.is_open():
            self.open_here()

    def move_left(self):
        assert self.walker.frames and self.walker.frames[-1][0] == 1
        self.up()
        if not self.walker.frames:  # at hub: clamp to first tape cell
            self.down(1)

    def step(self):
        if self.halted:
            return False
        symbol = self.read()
        rule = self.program.get((self.state, symbol))
        if rule is None:
            while self.walker.frames:
                self.up()
            self.down(0)
            self.open_here()
            self.up()
            self.halted = True
            return False
        # Always create a version, so even a stuttering source transition
        # takes at least six native S contractions.
        self.write(rule.write)
        if rule.move == 1:
            self.move_right()
        elif rule.move == -1:
            self.move_left()
        else:
            assert rule.move == 0
        self.state = rule.next_state
        self.source_steps += 1
        return True

    def whole_term(self):
        return self.walker.whole_term(self.focus)

    def total_contractions(self):
        return self.trie.steps + self.walker.contractions

    def observe_term(self):
        return decode_bare_term(self.trie, self.whole_term())

    def head_index_for_test(self):
        # This diagnostic inspects the zipper; the machine never computes it.
        assert all(side == 1 for side, _, _ in self.walker.frames)
        return len(self.walker.frames) - 1


def decode_bare_term(trie, root):
    """Decode the bare S tree without source state, program or cursor.

    Return the fixed halt flag and all allocated binary tape cells. Every
    loop follows a proper child of a finite tree.
    """
    p = trie.p
    for side in trie.body_path:
        pair = p.nodes[root]
        if pair is None:
            return None
        root = pair[side]
    hub = trie.parse_protected(root)
    if hub is None:
        return None
    halt = trie.parse_protected(hub[0]) is not None
    current = hub[1]
    tape = []
    while True:
        cell = trie.parse_protected(current)
        if cell is None:
            break
        version = cell[0]
        bit = 0
        while True:
            record = trie.parse_protected(version)
            if record is None:
                break
            bit = int(trie.parse_protected(record[1]) is not None)
            version = record[0]
        tape.append(bit)
        current = cell[1]
    return halt, tuple(tape)


def term_digest(pool, term):
    cache = {pool.S: sha256(b'S').digest()}
    def digest(node):
        if node not in cache:
            left, right = pool.nodes[node]
            cache[node] = sha256(b'A' + digest(left) + digest(right)).digest()
        return cache[node]
    return digest(term)


def check_against_path_simulator(program, word, limit, audit_every_contraction=False):
    cursor = CursorMachine(program, word)
    reference = STapeMachine(program, word)
    if audit_every_contraction:
        cursor.walker.trace = []
        reference.trie.trace = []
    assert cursor.initial_contractions == reference.initial_native_steps
    checked = 0
    for source_state, source_head, source_tape, source_halted in reference_turing(program, word, limit):
        assert cursor.state == reference.state
        assert cursor.head_index_for_test() == len(reference.cell) - 1
        assert cursor.read() == reference.read()
        observed = cursor.observe_term()
        assert observed is not None and not observed[0]
        assert observed[1] == reference.read_prefix(len(observed[1]))
        assert cursor.state == source_state and cursor.head_index_for_test() == source_head
        prefix = max([source_head, len(word), *source_tape.keys()], default=0) + 2
        assert reference.read_prefix(prefix) == tuple(source_tape.get(i, 0) for i in range(prefix))
        assert term_digest(cursor.trie.p, cursor.whole_term()) == term_digest(reference.trie.p, reference.trie.term)
        before = cursor.total_contractions()
        a, b = cursor.step(), reference.step()
        assert a == b
        assert a != source_halted
        assert cursor.total_contractions() == reference.trie.steps
        assert term_digest(cursor.trie.p, cursor.whole_term()) == term_digest(reference.trie.p, reference.trie.term)
        checked += 1
        if a:
            assert 6 <= cursor.total_contractions() - before <= 21
            assert cursor.observe_term()[0] is False
        else:
            assert cursor.halted and reference.halt_marker()
            assert cursor.observe_term()[0] is True
            break
    if audit_every_contraction:
        assert len(cursor.walker.trace) == len(reference.trie.trace)
        for left, right in zip(cursor.walker.trace, reference.trie.trace):
            assert term_digest(cursor.trie.p, left) == term_digest(reference.trie.p, right)
    return cursor, checked


def main():
    demo_program = {(0, 1): Instruction(0, 0, 1),
                    (0, 0): Instruction(1, 1, -1)}
    demo, _ = check_against_path_simulator(demo_program, (1, 1, 1), 12, True)
    assert demo.halted and demo.source_steps == 4
    assert demo.observe_term() == (True, (0, 0, 0, 1))

    # A source stuttering loop must nevertheless perform unbounded S steps.
    loop_program = {(0, 0): Instruction(0, 0, 0)}
    loop, loop_checks = check_against_path_simulator(loop_program, (), 40, True)
    assert not loop.halted and loop.source_steps == 40
    assert loop.total_contractions() - loop.initial_contractions >= 6*40

    # Every one-state binary program, including both halt and all
    # write/move combinations, against all input words up to three bits.
    choices = [None] + [Instruction(0, b, d) for b in (0, 1) for d in (-1, 0, 1)]
    words = [word for size in range(4) for word in product((0, 1), repeat=size)]
    exhaustive = 0
    for zero, one in product(choices, repeat=2):
        p = {(0, bit): rule for bit, rule in enumerate((zero, one)) if rule is not None}
        for word in words:
            check_against_path_simulator(p, word, 8)
            exhaustive += 1

    rng = random.Random(20261027)
    snapshots = 0
    for _ in range(200):
        program = {}
        for state in range(3):
            for symbol in (0, 1):
                if rng.randrange(5):
                    program[state, symbol] = Instruction(rng.randrange(3),
                                                         rng.randrange(2),
                                                         rng.choice((-1, 0, 1)))
        word = tuple(rng.randrange(2) for _ in range(rng.randrange(5)))
        _, count = check_against_path_simulator(program, word, 12)
        snapshots += count
    print(json.dumps({'demo_source_steps': demo.source_steps,
                      'demo_s_contractions': demo.total_contractions(),
                      'demo_halts': demo.halted,
                      'stuttering_source_steps': loop_checks,
                      'stuttering_s_contractions': loop.total_contractions() - loop.initial_contractions,
                      'individual_s_steps_compared': len(demo.walker.trace) + len(loop.walker.trace),
                      'random_machines': 200,
                      'exhaustive_one_state_cases': exhaustive,
                      'checked_source_steps': snapshots,
                      'whole_s_tree_agreement': True}, indent=2))


if __name__ == '__main__':
    main()
