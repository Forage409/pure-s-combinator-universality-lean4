"""Read source output from S tape encoding a halted Neary configuration."""
from neary_output_reader import decode_halted_output
from s_finite_selector import Selector


def read_neary_source_output(program,runner):
    """Read committed bits only; caller must establish actual source halt."""
    probe=Selector(program,runner.trie,choose_only=True)
    pending=probe.find_status(True)
    assert pending is None
    active=probe.find_status(False)
    assert active is not None
    bit_head=len(probe.walker.frames)-1
    assert bit_head%4==0
    probe.to_hub()
    probe.down(1)
    bits=[]
    while probe.opened():
        bit,_,_=probe.read_cell()
        bits.append(bit)
        probe.down(1)
    symbols={}
    for i in range(0,len(bits),4):
        block=bits[i:i+4]
        block+= [0]*(4-len(block))
        value=0
        for bit in block: value=(value<<1)|bit
        if value: symbols[i//4]=value
    return decode_halted_output(symbols,bit_head//4)


def main():
    import json
    from binary_tm_compiler import encode_symbols
    from fast_initial_encoder import encode_initial
    from neary_u3_11 import encode_source,run_u
    from normalize_neary_safe import normalize_safe
    from prize_encoder import BINARY_UNIVERSAL
    from s_monotone_tape import Instruction
    source={(0,0):Instruction(1,1,0)}
    normalized,n,word=normalize_safe(source,2,())
    encoded,head=encode_source(normalized,n,word)
    steps,state,head,tape=run_u(encoded,head,2_000_000)
    assert steps is not None and state==2
    length=max(tape,default=0)+1
    utm_word=tuple(tape.get(i,0) for i in range(length))
    runner,stats=encode_initial(BINARY_UNIVERSAL,encode_symbols(utm_word,4),4*head)
    output=read_neary_source_output(BINARY_UNIVERSAL,runner)
    assert output==(1,)
    print(json.dumps({'universal_steps_to_halt':steps,
                      'artificially_reencoded_final_s_cells':stats['cells'],
                      'decoded_source_output':output,
                      's_tape_output_reader_agrees':True},indent=2))


if __name__=='__main__':main()
