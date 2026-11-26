"""Neary's one-sided U(3,11), Table 3.3.2, and its binary compilation.

Source: Turlough Neary, Small Universal Turing Machines, 2008 thesis,
Chapter 3, Definition 3.3.3 and Table 3.3.2, printed page 32 (PDF page 38):
https://gwern.net/doc/cs/computable/2008-neary.pdf

Names LA/LB/LE/LH and RE/RH denote the left/right arrow decorations. LA is
the blank. Each tuple is (written symbol, movement, next control state).
The single missing rule is U3 on DELTA. `encode_source` implements the
normalized-machine encoding in Definitions 3.2.1--3.2.2 and Equations
3.3.1--3.3.5, with the U3,11 head at the encoded current state.
"""
import json
from binary_tm_compiler import MultiInstruction, compile_machine, check_compilation

SYMBOLS=('LA','LB','E','H','RE','RH','LE','LH','LAMBDA','DELTA','GAMMA')
S={name:i for i,name in enumerate(SYMBOLS)}

# Rows follow Table 3.3.2; columns are U1, U2, U3.
ROWS={
    'LA':     (('LE',1,0),('GAMMA',-1,1),('LA',-1,2)),
    'LB':     (('LE',1,1),('LB',-1,0),('E',1,0)),
    'E':      (('RE',-1,0),('LE',1,0),('E',1,0)),
    'H':      (('RH',-1,0),('LH',1,2),('LA',-1,0)),
    'RE':     (('LE',1,0),('E',1,1),('LE',1,2)),
    'RH':     (('LH',1,0),('H',1,1),('LH',1,2)),
    'LE':     (('RE',-1,0),('RE',-1,1),('GAMMA',-1,1)),
    'LH':     (('RH',-1,0),('RH',-1,1),('LA',-1,2)),
    'LAMBDA': (('DELTA',1,0),('LAMBDA',1,1),('DELTA',1,2)),
    'DELTA':  (('LAMBDA',-1,0),('LAMBDA',-1,1),None),
    'GAMMA':  (('LA',-1,2),('LH',1,2),('LB',-1,2)),
}


def machine():
    out={}
    for read,row in ROWS.items():
        assert len(row)==3
        for state,cell in enumerate(row):
            if cell is not None:
                write,move,next_state=cell
                out[state,S[read]]=MultiInstruction(next_state,S[write],move)
    assert len(out)==32 and (2,S['DELTA']) not in out
    return out


def encode_source(program,state_count,word):
    """Encode Neary's normalized binary one-sided machine and input.

    States are 0..state_count-1; the final state must move left forever
    without changing either symbol. All other transitions must be defined,
    use L/R and stay within the state range, as in the thesis assumptions.
    """
    assert state_count>=2 and all(bit in (0,1) for bit in word)
    for q in range(state_count):
        for bit in (0,1):
            t=program[q,bit]
            assert t.write in (0,1) and t.move in (-1,1)
            assert 0<=t.next_state<state_count
            if q==state_count-1:
                assert (t.next_state,t.write,t.move)==(q,bit,-1)

    def exponents(t):
        b=2+5*t.next_state+(3 if t.move==-1 else 0)
        a=5*state_count+2-b
        assert a>=1 and b>=0
        return a,b

    def etr(t):
        a,b=exponents(t)
        if t.move==1:
            return ([S['H']] if t.write else [])+[S['E']]*a+[S['H']]*b
        return ([S['E']]*(a-1)+[S['H']]*b+
                ([S['E'],S['H'],S['E']] if t.write else [S['E']]*3))

    def extra(q):
        if q==0:
            return [S['E']]*(5*state_count-3)+[S['H']]*4
        incoming=[t for t in program.values() if t.next_state==q and t.move==1]
        if not incoming:
            return []
        a,b=exponents(incoming[0])
        assert a>=3
        return [S['E']]*(a-3)+[S['H']]*(b+2)

    prefix=[]
    for q in range(state_count-1,-1,-1):
        t0,t1=program[q,0],program[q,1]
        for part in (etr(t1),etr(t0),etr(t0),etr(t1),extra(q)):
            prefix += [S['LAMBDA']]+part
    prefix += [S['LAMBDA'],S['E']]
    head=len(prefix)
    current=[S['LA']]*(5*state_count)+[S['LB']]*2
    data=[]
    for bit in word:
        data += [S['LB'] if bit else S['LA'],S['LA']]
    return tuple(prefix+current+data),head


def run_u(word,head,max_steps):
    table=machine()
    tape={i:x for i,x in enumerate(word) if x}
    state=0
    for step in range(max_steps):
        instr=table.get((state,tape.get(head,0)))
        if instr is None:
            return step,state,head,tape
        if instr.write: tape[head]=instr.write
        else: tape.pop(head,None)
        state=instr.next_state
        head=max(0,head+instr.move)
    return None,state,head,tape


def main():
    source=machine()
    compiled,keys,width=compile_machine(source,len(SYMBOLS))
    assert width==4 and keys[0]==('read',0,0,0)
    checked=0
    for state in range(3):
        for symbol in range(len(SYMBOLS)):
            check_compilation(source,len(SYMBOLS),(symbol,),2,initial_state=state)
            checked+=1
    _,_,_,halted=check_compilation(source,len(SYMBOLS),(S['DELTA'],),2,initial_state=2)
    assert halted
    # Example 3.3.1: M1 on 101. Table 3.3.1 provides independent ETR values.
    m1={(0,0):MultiInstruction(1,1,1),(0,1):MultiInstruction(0,0,1),
        (1,0):MultiInstruction(1,0,-1),(1,1):MultiInstruction(2,1,-1),
        (2,0):MultiInstruction(2,0,-1),(2,1):MultiInstruction(2,1,-1)}
    encoded,head=encode_source(m1,3,(1,0,1))
    e,h,lam=S['E'],S['H'],S['LAMBDA']
    e31=[e]+[h]*15+[e,h,e]
    e30=[e]+[h]*15+[e,e,e]
    e21=e31
    e20=[e]*6+[h]*10+[e,e,e]
    e11=[e]*15+[h]*2
    e10=[h]+[e]*10+[h]*7
    etrs=[e31,e30,e30,e31,[],e21,e20,e20,e21,[e]*7+[h]*9,
          e11,e10,e10,e11,[e]*12+[h]*4]
    expected=[]
    for part in etrs: expected += [lam]+part
    expected += [lam,e]
    assert encoded[:head]==tuple(expected)
    halt_steps,_,_,_=run_u(encoded,head,1_000_000)
    assert halt_steps is not None
    print(json.dumps({'source_states':3,'source_symbols':len(SYMBOLS),
                      'source_rules':len(source),'binary_block_width':width,
                      'compiled_states':len(keys),'compiled_rules':len(compiled),
                      'source_state_symbol_cases_checked':checked,
                      'known_undefined_rule_halts':halted,
                      'example_encoded_symbols':len(encoded),
                      'example_utm_start_head':head,
                      'example_utm_halt_steps':halt_steps,
                      'normalized_universal_input_encoder_implemented':True},indent=2))


if __name__=='__main__':
    main()
