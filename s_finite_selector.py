"""Candidate fresh-root finite-control selector for the versioned S tape.

Each call starts at the root and performs one native S contraction, or
reports the fixed halt marker. The only unbounded working object is the
tree cursor/zipper; program state and metadata widths are fixed finite data.
The protected-trie local reductions are from Filin (2026).
"""
import json
import random
from s_boundary_reset import BoundaryMachine
from s_monotone_tape import Instruction, reference as source_reference
from s_cursor_tape import term_digest
from s_engine import DAGPool
from stateless_opening import next_address
from trie_walker import Walker


class Selector:
    def __init__(self, program, trie, choose_only=False):
        self.program = dict(program)
        states = [0]
        for (state, _), inst in self.program.items():
            states.extend((state,inst.next_state))
        self.width = max(1,max(states).bit_length())
        self.trie = trie
        self.walker = Walker(trie)
        self.last_redex_address = None
        self.choose_only = choose_only
        self.focus = trie.term
        self.walker.ambient = []
        for side in trie.body_path:
            l,r = trie.p.nodes[self.focus]
            self.walker.ambient.append((side,r if side==0 else l))
            self.focus = l if side==0 else r
        # The focus is now the opened hub; no source state has been supplied.
        assert self.opened()

    def opened(self):
        return self.trie.parse_protected(self.focus) is not None

    def down(self, side):
        node = self.trie.parse_protected(self.focus)
        assert node is not None
        l,r,junk = node
        self.walker.frames.append((side,r if side==0 else l,junk))
        self.focus = l if side==0 else r

    def up(self):
        side,sibling,junk = self.walker.frames.pop()
        self.focus = (self.trie.protected(self.focus,sibling,junk) if side==0
                      else self.trie.protected(sibling,self.focus,junk))

    def to_hub(self):
        while self.walker.frames:
            self.up()

    def one_native(self):
        local = next_address(self.trie,self.focus)
        assert local is not None
        address=[side for side,_ in self.walker.ambient]
        for side,_,_ in self.walker.frames:
            address.extend((0,1) if side==0 else (1,0,1))
        self.last_redex_address=tuple(address)+local
        if self.choose_only:
            return self.last_redex_address
        self.focus = self.walker.step_inside(self.focus,local)
        return self.walker.whole_term(self.focus)

    def read_version(self):
        """Focus on an opened version; return committed metadata or None."""
        self.down(1)
        climbs = 1  # at most width+4: a fixed finite controller counter
        bits = []
        for _ in range(self.width+3):
            if not self.opened():
                for _ in range(climbs):
                    self.up()
                return None
            self.down(0)
            bits.append(int(self.opened()))
            self.up()
            self.down(1)
            climbs += 1
        committed = self.opened()
        for _ in range(climbs):
            self.up()
        if not committed:
            return None
        state = 0
        for bit in bits[3:]:
            state = (state << 1) | bit
        return bits[0],2*bits[1]+bits[2],state

    def read_cell(self):
        """Read latest committed value and return focus to the tape cell."""
        latest=(0,0,0)
        self.down(0)
        while self.opened():
            record=self.read_version()
            if record is not None:
                latest=record
            self.down(0)
        # Version descendants are left children; a tape cell is a right child.
        while self.walker.frames and self.walker.frames[-1][0]==0:
            self.up()
        assert self.walker.frames and self.walker.frames[-1][0]==1
        return latest

    def find_status(self, pending):
        """Two bounded scans avoid saving an unbounded table of tape cells."""
        self.to_hub()
        self.down(1)
        while self.opened():
            value=self.read_cell()
            if (value[1] in (2,3)) if pending else (value[1]==1):
                return value
            self.down(1)
        self.to_hub()
        return None

    def append_one(self, symbol, status, state):
        """At a cell, select exactly one next step of its intended record."""
        self.down(0)
        while self.opened():
            if self.read_version() is None:
                break
            self.down(0)
        if not self.opened():
            return self.one_native()
        desired=(symbol,status>>1,status&1)+tuple(
            (state>>i)&1 for i in range(self.width-1,-1,-1))
        self.down(1)
        for bit in desired:
            if not self.opened():
                return self.one_native()
            self.down(0)
            if bit and not self.opened():
                return self.one_native()
            assert bit or not self.opened()
            self.up()
            self.down(1)
        assert not self.opened()
        return self.one_native()

    def advance(self):
        # Fixed local halt flag at the left child of the hub.
        self.down(0)
        if self.opened():
            return None
        self.up()

        pending=self.find_status(True)
        if pending is not None:
            symbol,status,state=pending
            # A left-boundary move is never stored as pending.
            if status==3:
                self.down(1)
            else:
                self.up()
                assert self.walker.frames  # hub is not a tape cell
            if not self.opened():
                assert status==3
                return self.one_native()
            target_bit,target_status,target_state=self.read_cell()
            if target_status==1:
                assert target_state==state
                # Return to pending cell and finish its off-head record.
                if status==3:
                    self.up()
                else:
                    self.down(1)
                return self.append_one(symbol,0,0)
            assert target_status==0
            return self.append_one(target_bit,1,state)

        active=self.find_status(False)
        assert active is not None
        symbol,_,state=active
        inst=self.program.get((state,symbol))
        if inst is None:
            self.to_hub()
            self.down(0)
            return self.one_native()

        if inst.move == -1:
            self.up()
            first_cell = not self.walker.frames
            self.down(1)
        else:
            first_cell = False
        if inst.move==0 or (inst.move==-1 and first_cell):
            return self.append_one(inst.write,1,inst.next_state)
        return self.append_one(inst.write,2 if inst.move==-1 else 3,inst.next_state)


def select_address(program, pool, root):
    """Total selector interface on finite acyclic pure-S trees.

    It returns a literal redex address, a recognized halt event, or rejection
    of a malformed representation. The root itself is not rewritten here.
    """
    try:
        fresh=BoundaryMachine.resume_from_term(program,pool,root)
        selector=Selector(program,fresh.trie,choose_only=True)
        address=selector.advance()
        return ('halt',None) if address is None else ('step',address)
    except (AssertionError,IndexError,KeyError,TypeError,ValueError,RecursionError):
        return ('reject',None)


def verify(program, word, limit):
    reference=BoundaryMachine(program,word)
    source_trace=source_reference(program,word,200)
    checked=source_steps=since_boundary=0
    d=reference.width+3
    source_step_upper_bound=7*(3*(2*d+2)+1)
    for _ in range(limit):
        kind,address=select_address(program,reference.trie.p,reference.trie.term)
        assert kind=='step' and address is not None
        fresh=BoundaryMachine.resume_from_term(program,reference.trie.p,reference.trie.term)
        # Only this independently checked operation mutates the logical term.
        fresh.trie.contract(address)
        actual=fresh.trie.term
        expected_result=reference.advance_native()
        assert actual is not None
        assert actual == reference.trie.term
        checked+=1
        since_boundary+=1
        source_steps += expected_result=='complete'
        if expected_result=='complete':
            assert 6 <= since_boundary <= source_step_upper_bound
            since_boundary=0
        # Whenever the bare tree exposes a stable source boundary, it must
        # agree with the ordinary source run, even at intermediate S steps.
        halt,cells,heads,pending=reference.observe()
        if not pending and len(heads)==1 and source_steps < len(source_trace):
            expected_state,expected_head,expected_tape,_=source_trace[source_steps]
            assert heads[0] == ((1,)*(expected_head+1),expected_state)
            bits=[record[0] for _,record in cells]
            for position in range(max([expected_head,*expected_tape.keys()],default=0)+1):
                assert (bits[position] if position < len(bits) else 0) == expected_tape.get(position,0)
        if expected_result=='halt':
            assert since_boundary <= 7
            assert source_steps < len(source_trace) and source_trace[source_steps][3]
            assert Selector(program,reference.trie).advance() is None
            return checked,source_steps,True
    return checked,source_steps,False


def verify_without_prior_pool(program,word,interval=7,limit=1000):
    """Rebuild reachable bare term in an empty pool at sampled native steps."""
    reference=BoundaryMachine(program,word)
    samples=0
    for index in range(limit):
        old_pool,root=reference.trie.p,reference.trie.term
        next_in_fresh=None
        fresh_pool=None
        if index % interval == 0:
            fresh_pool=DAGPool()
            memo={old_pool.S:fresh_pool.S}
            def copy(node):
                if node not in memo:
                    left,right=old_pool.nodes[node]
                    memo[node]=fresh_pool.app(copy(left),copy(right))
                return memo[node]
            fresh_root=copy(root)
            fresh=BoundaryMachine.resume_from_term(program,fresh_pool,fresh_root)
            next_in_fresh=Selector(program,fresh.trie).advance()
            assert next_in_fresh is not None
            samples+=1
        result=reference.advance_native()
        if fresh_pool is not None:
            assert term_digest(fresh_pool,next_in_fresh)==term_digest(old_pool,reference.trie.term)
        if result=='halt':
            return samples,index+1,True
    return samples,limit,False


def main():
    demo={(0,1):Instruction(0,0,1),(0,0):Instruction(1,1,-1)}
    checked,steps,halted=verify(demo,(1,1,1),1000)
    assert halted and steps==4
    isolated_samples,isolated_steps,isolated_halted=verify_without_prior_pool(
        demo,(1,1,1))
    assert isolated_halted and isolated_steps==checked
    loop={(0,0):Instruction(0,0,0)}
    loop_checked,loop_steps,loop_halted=verify(loop,(),200)
    assert not loop_halted and loop_steps>0
    # Bidirectional moves, writes of both bits, and multi-state transitions.
    overwrite={(0,0):Instruction(1,1,1),(1,0):Instruction(2,1,-1),
               (2,1):Instruction(3,0,1),(3,1):Instruction(4,0,-1)}
    overwrite_checked,overwrite_steps,overwrite_halted=verify(overwrite,(),1500)
    assert overwrite_halted and overwrite_steps==4
    rng=random.Random(20261027)
    random_native=random_sources=0
    for _ in range(30):
        program={}
        for state in range(3):
            for symbol in (0,1):
                if rng.randrange(5):
                    program[state,symbol]=Instruction(rng.randrange(3),
                                                       rng.randrange(2),
                                                       rng.choice((-1,0,1)))
        word=tuple(rng.randrange(2) for _ in range(rng.randrange(4)))
        count,source_count,_=verify(program,word,200)
        random_native+=count
        random_sources+=source_count
    print(json.dumps({'demo_native_steps':checked,'demo_source_steps':steps,
                      'demo_halted':halted,'loop_native_steps':loop_checked,
                      'fresh_pool_samples':isolated_samples,
                      'loop_source_steps':loop_steps,
                      'overwrite_native_steps':overwrite_checked,
                      'overwrite_source_steps':overwrite_steps,
                      'random_programs':30,'random_native_steps':random_native,
                      'random_completed_source_steps':random_sources,
                      'each_selector_started_at_root':True,
                      'exact_tree_agreement':True},indent=2))


if __name__=='__main__':
    main()
