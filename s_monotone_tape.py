"""A source-dependent tape stored in a pure-S protected trie.

Protected-node opening uses Filin's 2026 six/seven native S contractions.
This separate experiment stores tape cells and append-only versions directly
in those nodes. The controller carries a finite machine state and one tree
cursor; every memory write is an actual S contraction. See the accompanying
research note for the exact scope and remaining formal obligations.
"""
from dataclasses import dataclass
import json
import random
from trie_generator import Trie


@dataclass(frozen=True)
class Instruction:
    next_state: int
    write: int
    move: int  # -1, 0, +1; head clamps at the left boundary.


class STapeMachine:
    def __init__(self, program, input_word):
        self.program = program
        self.trie = Trie()
        self.trie.bootstrap_ten_leaf_seed()
        self.state = 0
        self.cell = (1,)  # root's right child starts the tape backbone
        self.steps = 0
        self.halted = False
        self._open(())       # hub: left child is reserved as the halt marker
        self._open(self.cell)
        for index, bit in enumerate(input_word):
            if index:
                self.cell += (1,)
                self._open(self.cell)
            if bit:
                self.write(1)
        self.cell = (1,)
        self.initial_native_steps = self.trie.steps

    def _physical(self, address):
        path = self.trie.body_path
        for bit in address:
            path = self.trie.child_path(path, bit)
        return path

    def _is_open(self, address):
        term = self.trie.at(self._physical(address))
        return self.trie.parse_protected(term) is not None

    def _open(self, address):
        path = self._physical(address)
        assert not self._is_open(address)
        self.trie.open_local(path)
        assert self._is_open(address)

    def _latest_version(self):
        """Walk left from a tape cell to the first unused version slot."""
        slot = self.cell + (0,)
        last = None
        while self._is_open(slot):
            last = slot
            slot += (0,)
        return last, slot

    def read(self):
        last, _ = self._latest_version()
        return int(last is not None and self._is_open(last + (1,)))

    def write(self, bit):
        assert bit in (0, 1)
        _, slot = self._latest_version()
        self._open(slot)
        if bit:
            self._open(slot + (1,))
        assert self.read() == bit

    def step(self):
        if self.halted:
            return False
        value = self.read()
        instruction = self.program.get((self.state, value))
        if instruction is None:
            # A fixed structural flag in the S term exposes source halting.
            self._open((0,))
            self.halted = True
            assert self.halt_marker()
            return False
        assert instruction.write in (0, 1) and instruction.move in (-1, 0, 1)
        # Even a no-op write appends a fresh version. Each source step then
        # causes at least one genuine S reduction, including stuttering loops.
        self.write(instruction.write)
        if instruction.move == 1:
            self.cell += (1,)
            if not self._is_open(self.cell):
                self._open(self.cell)
        elif instruction.move == -1 and self.cell != (1,):
            self.cell = self.cell[:-1]
        self.state = instruction.next_state
        self.steps += 1
        return True

    def halt_marker(self):
        return self._is_open((0,))

    def read_prefix(self, count):
        saved = self.cell
        bits = []
        path = (1,)
        for index in range(count):
            if not self._is_open(path):
                bits.extend([0] * (count - index))
                break
            else:
                self.cell = path
                bits.append(self.read())
            path += (1,)
        self.cell = saved
        return tuple(bits)


def reference(program, input_word, limit):
    tape = {i: bit for i, bit in enumerate(input_word) if bit}
    state = head = 0
    snapshots = []
    for _ in range(limit):
        snapshots.append((state, head, dict(tape), False))
        rule = program.get((state, tape.get(head, 0)))
        if rule is None:
            snapshots[-1] = (state, head, dict(tape), True)
            break
        if rule.write:
            tape[head] = 1
        else:
            tape.pop(head, None)
        state = rule.next_state
        head = max(0, head + rule.move)
    return snapshots


def check(program, input_word, limit):
    expected = reference(program, input_word, limit)
    actual = STapeMachine(program, input_word)
    for state, head, tape, halted in expected:
        assert actual.state == state
        assert len(actual.cell) - 1 == head
        prefix = max([head, len(input_word), *tape.keys()], default=0) + 2
        assert actual.read_prefix(prefix) == tuple(tape.get(i, 0) for i in range(prefix))
        assert actual.read() == tape.get(head, 0)
        if halted:
            assert not actual.step() and actual.halt_marker()
            break
        assert actual.step()
        assert not actual.halt_marker()
    return actual, len(expected)


def main():
    # Writes both symbols, walks across cells and halts.
    program = {
        (0, 1): Instruction(0, 0, 1),
        (0, 0): Instruction(1, 1, -1),
    }
    demo, checked = check(program, (1, 1, 1), 12)
    assert demo.halted and demo.read_prefix(5) == (0, 0, 0, 1, 0)

    # Explicitly overwrite each cell 0->1->0 while walking both ways.
    overwrite = {
        (0, 0): Instruction(1, 1, 1),
        (1, 0): Instruction(2, 1, -1),
        (2, 1): Instruction(3, 0, 1),
        (3, 1): Instruction(4, 0, -1),
    }
    other, _ = check(overwrite, (), 12)
    assert other.halted and other.read_prefix(3) == (0, 0, 0)

    rng = random.Random(20261027)
    runs = checked_snapshots = 0
    for _ in range(200):
        generated = {}
        for state in range(3):
            for bit in (0, 1):
                if rng.randrange(5):
                    generated[state, bit] = Instruction(rng.randrange(3),
                                                        rng.randrange(2),
                                                        rng.choice((-1, 0, 1)))
        word = tuple(rng.randrange(2) for _ in range(rng.randrange(5)))
        machine, count = check(generated, word, 12)
        runs += 1
        checked_snapshots += count

    print(json.dumps({'example_input': '111',
                      'example_output': ''.join(map(str, demo.read_prefix(5))),
                      'example_machine_steps': demo.steps,
                      'example_initial_s_steps': demo.initial_native_steps,
                      'example_total_s_steps': demo.trie.steps,
                      'halt_visible_in_s_term': demo.halt_marker(),
                      'random_machines': runs,
                      'checked_machine_snapshots': checked_snapshots,
                      'overwrite_test_passed': other.halted}, indent=2))


if __name__ == '__main__':
    main()
