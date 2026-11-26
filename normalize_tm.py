"""Normalize partial binary machines to Neary's total L/R format.

WARNING: Do not compose this normalizer directly with Neary U(3,11): that
underlying simulator halts at a nonfinal left-boundary move. Use
normalize_neary_safe.py for the universal encoding.

The normalized machine has a distinguished last state representing source
termination. At boundaries between source steps, state, tape and head agree.
"""
from itertools import product
import json
from s_monotone_tape import Instruction


def normalize(program, state_count):
    assert state_count >= 1
    for (q, bit), rule in program.items():
        assert 0 <= q < state_count and bit in (0, 1)
        assert 0 <= rule.next_state < state_count
        assert rule.write in (0, 1) and rule.move in (-1, 0, 1)
    out = {}
    aux = {}
    for q in range(state_count):
        for bit in (0, 1):
            t = program.get((q, bit))
            if t is not None and t.move == 0:
                aux[q, bit] = state_count + len(aux)
    halt = state_count + len(aux)
    for q in range(state_count):
        for bit in (0, 1):
            t = program.get((q, bit))
            if t is None:
                out[q, bit] = Instruction(halt, bit, -1)
            elif t.move:
                out[q, bit] = t
            else:
                a = aux[q, bit]
                out[q, bit] = Instruction(a, t.write, 1)
                for observed in (0, 1):
                    out[a, observed] = Instruction(t.next_state, observed, -1)
    for bit in (0, 1):
        out[halt, bit] = Instruction(halt, bit, -1)
    return out, halt + 1


def advance(program, state, head, tape):
    bit = tape.get(head, 0)
    t = program.get((state, bit))
    if t is None:
        return None
    tape = dict(tape)
    if t.write: tape[head] = 1
    else: tape.pop(head, None)
    return t.next_state, max(0, head + t.move), tape


def main():
    choices = [None] + [Instruction(0, bit, move)
                        for bit in (0, 1) for move in (-1, 0, 1)]
    cases = 0
    for transitions in product(choices, repeat=2):
        program = {(0, bit): t for bit, t in enumerate(transitions) if t is not None}
        normalized, n = normalize(program, 1)
        for length in range(3):
            for word in product((0, 1), repeat=length):
                tape = {i: bit for i, bit in enumerate(word) if bit}
                source = (0, 0, tape)
                compiled = (0, 0, dict(tape))
                for _ in range(20):
                    next_source = advance(program, *source)
                    if next_source is None:
                        next_compiled = advance(normalized, *compiled)
                        assert next_compiled[0] == n - 1
                        assert next_compiled[2] == source[2]
                        break
                    compiled = advance(normalized, *compiled)
                    if compiled[0] >= 1 and compiled[0] != n - 1:
                        compiled = advance(normalized, *compiled)
                    assert compiled == next_source
                    source = next_source
                cases += 1
    print(json.dumps({'machines_and_inputs': cases, 'source_steps_compared': 20,
                      'source_boundary_states_agree': True}))


if __name__ == '__main__':
    main()

