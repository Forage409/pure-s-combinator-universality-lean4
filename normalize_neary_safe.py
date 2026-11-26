"""Compile clamped one-sided binary machines to Neary-safe machines.

Neary U(3,11) can halt on a simulated left move at the tape's left end,
even when the source control state is nonfinal. A marked, interleaved tape prevents
such moves during ordinary execution; only the designated halt state may
walk off the left end.
"""
from itertools import product
import json
from s_monotone_tape import Instruction
from normalize_tm import advance


def normalize_safe(program, state_count, word):
    word = tuple(word)
    assert state_count >= 1 and all(b in (0,1) for b in word)
    for (q,b),t in program.items():
        assert 0 <= q < state_count and b in (0,1)
        assert 0 <= t.next_state < state_count
        assert t.write in (0,1) and t.move in (-1,0,1)
    # State 0 moves from the boundary marker to source cell 0. Source
    # controls are shifted by one, preserving their identity at boundaries.
    out={(0,b):Instruction(1,b,1) for b in (0,1)}
    aux={}
    for (q,b),t in sorted(program.items()):
        aux[q,b]=state_count+1+len(aux)
    halt=state_count+1+len(aux)
    for q in range(state_count):
        for b in (0,1):
            t=program.get((q,b))
            if t is None:
                out[q+1,b]=Instruction(halt,b,-1)
                continue
            a=aux[q,b]
            first_move=-1 if t.move==-1 else 1
            out[q+1,b]=Instruction(a,t.write,first_move)
            for marker in (0,1):
                if t.move==-1:
                    second_move=1 if marker else -1
                elif t.move==1:
                    second_move=1
                else:
                    second_move=-1
                out[a,marker]=Instruction(t.next_state+1,marker,second_move)
    for b in (0,1): out[halt,b]=Instruction(halt,b,-1)
    initial=[1]
    for i,b in enumerate(word if word else (0,)):
        if i: initial.append(0)
        initial.append(b)
    return out,halt+1,tuple(initial)


def main():
    choices=[None]+[Instruction(0,b,m) for b in (0,1) for m in (-1,0,1)]
    checked=0
    for transitions in product(choices,repeat=2):
        p={(0,b):t for b,t in enumerate(transitions) if t is not None}
        for length in range(3):
            for word in product((0,1),repeat=length):
                norm,n,w=normalize_safe(p,1,word)
                s=(0,0,{i:b for i,b in enumerate(word) if b})
                c=(0,0,{i:b for i,b in enumerate(w) if b})
                c=advance(norm,*c)
                for _ in range(30):
                    assert c[0]==s[0]+1 and c[1]==2*s[1]+1
                    assert c[2].get(0,0)==1
                    for i in range(max([len(word),s[1]+1,*[j+1 for j in s[2]]],default=1)+2):
                        assert c[2].get(2*i+1,0)==s[2].get(i,0)
                        if i: assert c[2].get(2*i,0)==0
                    nxt=advance(p,*s)
                    if nxt is None:
                        c=advance(norm,*c)
                        assert c[0]==n-1
                        break
                    c=advance(norm,*c)
                    # The first step always lands on a marker and the
                    # second returns to a source-data position.
                    assert c[0] >= 1+1 and c[0] < n-1
                    assert c[1] >= 0
                    c=advance(norm,*c)
                    s=nxt
                checked+=1
    print(json.dumps({'machine_input_cases':checked,'source_steps_bound':30,
                      'marked_boundary_compilation_agrees':True}))


if __name__=='__main__': main()
