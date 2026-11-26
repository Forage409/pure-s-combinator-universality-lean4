"""Compose a fixed S simulation with an arbitrary binary machine input.

The machine used by the selector is fixed once and for all; only the initial
S term depends on the encoded source machine and input.
"""
import json
from binary_tm_compiler import compile_machine, encode_symbols
from fast_initial_encoder import encode_initial
from neary_u3_11 import machine, encode_source
from normalize_neary_safe import normalize_safe
from s_monotone_tape import Instruction

BINARY_UNIVERSAL, CONTROL_STATES, BLOCK_WIDTH = compile_machine(machine(), 11)


def encode_instance(source_program, source_state_count, input_word):
    normalized, state_count, marked_word = normalize_safe(source_program, source_state_count, input_word)
    symbols, head = encode_source(normalized, state_count, marked_word)
    bits = encode_symbols(symbols, BLOCK_WIDTH)
    runner, stats = encode_initial(BINARY_UNIVERSAL, bits, head * BLOCK_WIDTH)
    stats.update({'normalized_source_states': state_count,
                  'universal_tape_symbols': len(symbols),
                  'universal_head': head,
                  'binary_head': head * BLOCK_WIDTH})
    return runner, stats


def main():
    # A machine that writes one, stays, then halts; normalized encoding must
    # introduce a move-right/move-left pair and a final halt state.
    source = {(0, 0): Instruction(1, 1, 0)}
    runner, stats = encode_instance(source, 2, (0, 1))
    assert BLOCK_WIDTH == 4 and len(CONTROL_STATES) == 132
    assert stats['normalized_source_states'] == 5
    assert runner.program == BINARY_UNIVERSAL
    print(json.dumps({'fixed_binary_states': len(CONTROL_STATES),
                      'fixed_binary_rules': len(BINARY_UNIVERSAL),
                      'example_encoding': stats}, indent=2))


if __name__ == '__main__':
    main()

