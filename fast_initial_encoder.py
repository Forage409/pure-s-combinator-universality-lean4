"""Construct the initial S tape bottom-up without replaying every opening.

Each opened F node is exactly the result of the published protected-trie
opening for its depth phase. The output denotes the same finite unfolded S
tree as sequential opening, but hash-consing avoids rebuilding every ancestor
after every encoder operation. No mutation is performed after encoding.
"""
import json
from itertools import product
from s_boundary_reset import BoundaryMachine
from s_cursor_tape import term_digest
from s_monotone_tape import Instruction
from trie_generator import Trie


def encode_initial(program, word, head_index=0):
    assert head_index>=0 and all(bit in (0,1) for bit in word)
    states=[0]
    for (state,_),rule in program.items():
        states.extend((state,rule.next_state))
    width=max(1,max(states).bit_length())

    def node():
        return [None,None]

    # Abstract open-node tree: hub.left is halt, hub.right is tape cell 0.
    hub=node()
    cell=node()
    hub[1]=cell
    count=max(1,len(word),head_index+1)
    for i in range(count):
        if i:
            cell[1]=node()
            cell=cell[1]
        bit=word[i] if i<len(word) else 0
        if bit or i==head_index:
            version=node()
            cell[0]=version
            fields=(bit,0,int(i==head_index))+(0,)*width
            parent=version
            for flag in fields:
                field=node()
                parent[1]=field
                if flag:
                    field[0]=node()
                parent=field
            parent[1]=node()  # committed record

    trie=Trie()
    trie.bootstrap_ten_leaf_seed()
    phases=[(2,2)]
    def phase(depth):
        while len(phases)<=depth:
            m,n=phases[-1]
            phases.append((m-1,n) if m else (n,n+1))
        return phases[depth]

    # Iterative postorder avoids recursion limits on long input backbones.
    built={}
    stack=[(hub,0,False)]
    opened=0
    while stack:
        current,depth,ready=stack.pop()
        if not ready:
            stack.append((current,depth,True))
            for child in current:
                if child is not None:
                    stack.append((child,depth+1,False))
            continue
        m,n=phase(depth)
        if m==0:
            m,n=n+1,n+1
        child=trie.generator(m-1,n)
        junk=trie.p.app(trie.p.app(trie.numeral(n-2),trie.S),child)
        left=built[id(current[0])] if current[0] is not None else child
        right=built[id(current[1])] if current[1] is not None else child
        built[id(current)]=trie.protected(left,right,junk)
        opened+=1
    trie.term=trie.replace(trie.term,trie.body_path,built[id(hub)])
    result=BoundaryMachine.resume_from_term(program,trie.p,trie.term)
    return result,{'cells':count,'opened_nodes':opened,
                   'dag_nodes':len(trie.p.nodes),'source_state_width':width}


def main():
    program={(0,0):Instruction(1,1,1),(1,1):Instruction(0,0,-1)}
    cases=0
    for length in range(4):
        for word in product((0,1),repeat=length):
            for head in range(max(1,length)+1):
                fast,_=encode_initial(program,word,head)
                slow=BoundaryMachine(program,word,head)
                assert term_digest(fast.trie.p,fast.trie.term)==term_digest(slow.trie.p,slow.trie.term)
                assert fast.observe()==slow.observe()
                cases+=1
    print(json.dumps({'small_encodings_compared':cases,
                      'literal_tree_and_decoding_agree':True},indent=2))


if __name__=='__main__':
    main()
