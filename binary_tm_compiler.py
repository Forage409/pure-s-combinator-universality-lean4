"""Compile finite-alphabet one-sided Turing machines to binary tape machines.

Each source tape symbol is represented by a fixed-width binary block, with
blank 0 encoded by an all-zero block. The generated finite-state machine reads
and writes one block, then moves exactly one block left/right or stays.
"""
from collections import deque
from dataclasses import dataclass
import json
from itertools import product
from s_monotone_tape import Instruction


@dataclass(frozen=True)
class MultiInstruction:
    next_state: int
    write: int
    move: int


def compile_machine(program, symbol_count, initial_state=0):
    assert symbol_count >= 2
    width=max(1,(symbol_count-1).bit_length())
    states={}
    inverse=[]
    pending=deque()
    output={}

    def intern(key):
        if key not in states:
            states[key]=len(inverse)
            inverse.append(key)
            pending.append(key)
        return states[key]

    start=intern(('read',initial_state,0,0))
    assert start==0
    while pending:
        key=pending.popleft()
        sid=states[key]
        for bit in (0,1):
            if key[0]=='read':
                _,q,i,prefix=key
                v=2*prefix+bit
                if i+1 < width:
                    new=('read',q,i+1,v)
                    output[sid,bit]=Instruction(intern(new),bit,1)
                    continue
                rule=program.get((q,v)) if v < symbol_count else None
                if rule is None:
                    # Return to the start of the source block before halting.
                    if width>1:
                        new=('halt',) if width==2 else ('rewind',width-2)
                        output[sid,bit]=Instruction(intern(new),bit,-1)
                    continue
                assert 0<=rule.write<symbol_count and rule.move in (-1,0,1)
                if width==1:
                    new=('read',rule.next_state,0,0)
                    output[sid,bit]=Instruction(intern(new),rule.write,rule.move)
                else:
                    lastbit=rule.write&1
                    new=('write',rule.next_state,rule.write,rule.move,width-2)
                    output[sid,bit]=Instruction(intern(new),lastbit,-1)
            elif key[0]=='write':
                _,q,value,direction,i=key
                newbit=(value >> (width-1-i))&1
                if i>0:
                    new=('write',q,value,direction,i-1)
                    output[sid,bit]=Instruction(intern(new),newbit,-1)
                elif direction==0:
                    output[sid,bit]=Instruction(intern(('read',q,0,0)),newbit,0)
                else:
                    new=('shift',q,direction,width-1)
                    output[sid,bit]=Instruction(intern(new),newbit,direction)
            elif key[0]=='shift':
                _,q,direction,remaining=key
                new=('read',q,0,0) if remaining==1 else ('shift',q,direction,remaining-1)
                output[sid,bit]=Instruction(intern(new),bit,direction)
            elif key[0]=='rewind':
                remaining=key[1]
                new=('halt',) if remaining==1 else ('rewind',remaining-1)
                output[sid,bit]=Instruction(intern(new),bit,-1)
            else:
                assert key == ('halt',)
    return output,tuple(inverse),width


def encode_symbols(symbols,width):
    return tuple((symbol >> shift)&1 for symbol in symbols
                 for shift in range(width-1,-1,-1))


def direct_step(program,state,head,tape):
    rule=program.get((state,tape.get(head,0)))
    if rule is None:
        return None
    updated=dict(tape)
    if rule.write: updated[head]=rule.write
    else: updated.pop(head,None)
    return rule.next_state,max(0,head+rule.move),updated


def check_compilation(program,symbol_count,word,steps,initial_state=0):
    compiled,keys,width=compile_machine(program,symbol_count,initial_state)
    source_tape={i:a for i,a in enumerate(word) if a}
    bits=encode_symbols(word,width)
    binary_tape={i:a for i,a in enumerate(bits) if a}
    sq,sh,bq,bh=initial_state,0,0,0
    for _ in range(steps):
        assert keys[bq]==('read',sq,0,0)
        assert bh==width*sh
        maxcell=max([sh,*source_tape.keys(),*(i//width for i in binary_tape)],default=0)+1
        for cell in range(maxcell):
            actual=0
            for i in range(width):
                actual=2*actual+binary_tape.get(width*cell+i,0)
            assert actual==source_tape.get(cell,0)
        nxt=direct_step(program,sq,sh,source_tape)
        micros=0
        while True:
            rule=compiled.get((bq,binary_tape.get(bh,0)))
            if rule is None:
                assert nxt is None
                assert bh==width*sh
                return compiled,keys,width,True
            if rule.write: binary_tape[bh]=1
            else: binary_tape.pop(bh,None)
            bq,bh=rule.next_state,max(0,bh+rule.move)
            micros+=1
            assert micros <= 3*width+1
            if keys[bq][0]=='read' and keys[bq][2:]==(0,0):
                assert nxt is not None
                sq,sh,source_tape=nxt
                break
    return compiled,keys,width,False


def main():
    program={(0,1):MultiInstruction(1,2,1),
             (1,0):MultiInstruction(2,1,-1)}
    binary,keys,width,halted=check_compilation(program,3,(1,),10)
    assert halted and width==2

    # Exhaust the alphabet-level transition cases at both boundary cells.
    cases=interior_cases=0
    for symbols in (2,3,4,5):
        for read,write,move in product(range(symbols),range(symbols),(-1,0,1)):
            p={(0,read):MultiInstruction(1,write,move)}
            _,_,_,done=check_compilation(p,symbols,(read,),3)
            assert done
            cases+=1
            interior={(0,0):MultiInstruction(1,0,1),
                      (1,read):MultiInstruction(2,write,move)}
            _,_,_,done=check_compilation(interior,symbols,(0,read),4)
            assert done
            interior_cases+=1

    # Exercise the generated binary program through fresh-root S selection.
    from s_finite_selector import verify
    native,source_steps,source_halted=verify(binary,encode_symbols((1,),width),600)
    assert source_steps>0
    print(json.dumps({'source_symbols':3,'binary_block_width':width,
                      'generated_binary_states':len(keys),
                      'generated_binary_rules':len(binary),
                      'demo_halted':halted,
                      'one_transition_boundary_cases':cases,
                      'one_transition_interior_cases':interior_cases,
                      'fresh_root_s_steps':native,
                      'binary_source_steps_completed':source_steps,
                      'binary_source_halted_within_limit':source_halted},indent=2))


if __name__=='__main__':
    main()
