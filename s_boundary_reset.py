"""Recover source state and the next redex from the bare S tree.

Each tape version contains fixed-width metadata and an explicit commit flag.
Moving-head transactions retain their destination state and direction in a
committed pending record. The executor re-reads state/head from the bare term
after every native S reduction, including partially opened protected nodes.
The present scanner uses Python lists and must still be compiled to a finite
tree-walking selector for the complete complexity claim.
"""
import json
import random
from itertools import product
from s_monotone_tape import Instruction, reference
from stateless_opening import next_address
from trie_generator import Trie


class BoundaryMachine:
    def __init__(self, program, input_word, head_index=0):
        self.program = dict(program)
        assert head_index >= 0
        all_states = [0]
        for (state, _), inst in self.program.items():
            all_states.extend((state, inst.next_state))
        self.width = max(1, max(all_states).bit_length())
        self.trie = Trie()
        self.trie.bootstrap_ten_leaf_seed()
        self._open(())
        path = (1,)
        count=max(1,len(input_word),head_index+1)
        for index in range(count):
            if index:
                path += (1,)
            self._open(path)
            bit=input_word[index] if index<len(input_word) else 0
            if bit or index==head_index:
                self._append(path,bit,int(index==head_index),0)
        self.initial_native_steps = self.trie.steps
        self.single_native = True

    @classmethod
    def resume_from_term(cls, program, pool, root):
        """Rebuild executor from its fixed program and current bare S tree."""
        obj = cls.__new__(cls)
        obj.program = dict(program)
        states = [0]
        for (state, _), inst in obj.program.items():
            states.extend((state, inst.next_state))
        obj.width = max(1,max(states).bit_length())
        t = Trie.__new__(Trie)
        t.p,t.S = pool,pool.S
        t.b = pool.app(t.S,t.S)
        t.c = [pool.app_many(t.S,[t.b,t.b])]
        t.term,t.body_path,t.steps,t.trace = root,(1,),0,None
        obj.trie = t
        obj.initial_native_steps = 0
        obj.single_native = True
        return obj

    def _physical(self, address):
        path = self.trie.body_path
        for bit in address:
            path = self.trie.child_path(path, bit)
        return path

    def _is_open(self, address):
        term = self.trie.at(self._physical(address))
        return self.trie.parse_protected(term) is not None

    def _open(self, address):
        assert not self._is_open(address)
        path = self._physical(address)
        if getattr(self,'single_native',False):
            local = next_address(self.trie,self.trie.at(path))
            assert local is not None
            self.trie.contract(path+local)
        else:
            self.trie.open_local(path)
            assert self._is_open(address)
        return self._is_open(address)

    def _append(self, cell, symbol, status, state):
        """Status: 0 off, 1 active, 2 moving left, 3 moving right."""
        assert symbol in (0,1) and status in (0,1,2,3)
        assert 0 <= state < 1 << self.width
        slot = cell + (0,)
        while self._is_open(slot):
            slot += (0,)
        self._open(slot)
        metadata = (symbol, status >> 1, status & 1) + tuple((state >> i) & 1
                                          for i in range(self.width-1,-1,-1))
        field = slot + (1,)
        for bit in metadata:
            self._open(field)
            if bit:
                self._open(field + (0,))
            field += (1,)
        self._open(field)  # commit: a local, durable marker

    def _latest(self, cell):
        slot = cell + (0,)
        value = (0,0,0)
        while self._is_open(slot):
            record = self._committed(slot)
            if record is not None:
                value = record
            slot += (0,)
        return value

    def _committed(self, slot):
        field = slot + (1,)
        bits = []
        for _ in range(self.width + 3):
            if not self._is_open(field):
                return None
            bits.append(int(self._is_open(field + (0,))))
            field += (1,)
        if not self._is_open(field):
            return None
        state = 0
        for bit in bits[3:]:
            state = (state << 1) | bit
        return bits[0],2*bits[1]+bits[2],state

    def _append_one_opening(self, cell, symbol, status, state):
        """Resume an existing partial record or start one; open one node.

        Return True exactly when this opening commits the new record. The
        desired record is re-derived from existing committed machine state.
        """
        slot = cell + (0,)
        while self._is_open(slot) and self._committed(slot) is not None:
            slot += (0,)
        if not self._is_open(slot):
            self._open(slot)
            return False
        desired = (symbol, status >> 1, status & 1) + tuple(
            (state >> i) & 1 for i in range(self.width-1,-1,-1))
        field = slot + (1,)
        for bit in desired:
            if not self._is_open(field):
                self._open(field)
                return False
            mark = field + (0,)
            if bit and not self._is_open(mark):
                self._open(mark)
                return False
            assert bit or not self._is_open(mark)
            field += (1,)
        assert not self._is_open(field)
        return self._open(field)

    def observe(self):
        """Read all allocated cells and the active head from the S term."""
        halt = self._is_open((0,))
        cells = []
        path = (1,)
        while self._is_open(path):
            cells.append((path,self._latest(path)))
            path += (1,)
        heads = [(path,state) for path,(_,status,state) in cells if status == 1]
        pending = [(path,symbol,status,state) for path,(symbol,status,state)
                   in cells if status in (2,3)]
        return halt,cells,heads,pending

    def advance_opening(self):
        """Open one protected node after re-reading the whole term.

        Return 'working', 'complete', or 'halt'. One opening still consists
        of six or seven S reductions with retained local control.
        """
        halt,cells,heads,pending = self.observe()
        if halt:
            return 'halt'
        assert len(pending) <= 1
        if pending:
            cell,symbol,status,state = pending[0]
            target = cell + (1,) if status == 3 else cell[:-1]
            assert target
            if not self._is_open(target):
                self._open(target)
                return 'working'
            target_bit,target_status,target_state = self._latest(target)
            if target_status == 1:
                assert target_state == state
                done = self._append_one_opening(cell,symbol,0,0)
                return 'complete' if done else 'working'
            assert target_status == 0
            self._append_one_opening(target,target_bit,1,state)
            return 'working'
        assert len(heads) == 1
        cell,state = heads[0]
        symbol = next(record[0] for path,record in cells if path == cell)
        inst = self.program.get((state,symbol))
        if inst is None:
            return 'halt' if self._open((0,)) else 'working'
        assert inst.move in (-1,0,1)
        if inst.move == 0 or (inst.move == -1 and cell == (1,)):
            done = self._append_one_opening(cell,inst.write,1,inst.next_state)
            return 'complete' if done else 'working'
        else:
            status = 2 if inst.move == -1 else 3
            self._append_one_opening(cell,inst.write,status,inst.next_state)
            return 'working'

    def step(self):
        while True:
            result = self.advance_native()
            if result == 'complete':
                return True
            if result == 'halt':
                return False

    def advance_native(self):
        """Select and perform one native step using the current bare tree."""
        if self._is_open((0,)):
            return 'halt'
        before = self.trie.steps
        result = self.advance_opening()
        assert self.trie.steps == before+1
        return result


def check(program, word, limit):
    actual = BoundaryMachine(program,word)
    expected = reference(program,word,limit)
    for state,head,tape,halted in expected:
        flag,cells,heads,pending = actual.observe()
        assert not flag and len(heads)==1
        assert not pending
        path,actual_state = heads[0]
        assert len(path)-1 == head and actual_state == state
        actual_bits = tuple(record[0] for _,record in cells)
        bound = max([head,len(word),*tape.keys()],default=0)+1
        for i in range(bound):
            assert (actual_bits[i] if i<len(actual_bits) else 0)==tape.get(i,0)
        assert actual.step() != halted
        if halted:
            assert actual.observe()[0]
            break
    return actual,len(expected)


def verify_atomic_cell_commit():
    """Check all intermediate S reductions of one metadata transaction."""
    machine = BoundaryMachine({(0,0):Instruction(1,1,0)},())
    machine.single_native = False
    old = machine._latest((1,))
    assert old == (0,1,0)
    machine.trie.trace = []
    slot = (1,0)
    while machine._is_open(slot):
        slot += (0,)

    def checked_open(address, expected_final):
        start = len(machine.trie.trace)
        machine._open(address)
        final = machine.trie.term
        steps = machine.trie.trace[start:]
        assert len(steps) in (6,7)
        for index, term in enumerate(steps):
            machine.trie.term = term
            expected = expected_final if index == len(steps)-1 else old
            assert machine._latest((1,)) == expected
        machine.trie.term = final

    checked_open(slot,old)
    field=slot+(1,)
    for bit in (1,0,1,1):
        checked_open(field,old)
        if bit:
            checked_open(field+(0,),old)
        field+=(1,)
    checked_open(field,(1,1,1))
    assert machine._latest((1,))==(1,1,1)
    return len(machine.trie.trace)


def verify_fresh_restart(program, word, native_limit):
    """Discard executor and rebuild from fixed program + bare tree each step."""
    machine = BoundaryMachine(program,word)
    pool = machine.trie.p
    checked = completed = 0
    for _ in range(native_limit):
        root = machine.trie.term
        rebuilt = BoundaryMachine.resume_from_term(program,pool,root)
        result = machine.advance_native()
        recovered_result = rebuilt.advance_native()
        assert result == recovered_result
        assert machine.trie.term == rebuilt.trie.term
        machine = rebuilt
        checked += 1
        completed += result == 'complete'
        if result == 'halt':
            assert machine.observe()[0]
            break
    return checked, completed, machine.observe()[0]


def main():
    demo_program={(0,1):Instruction(0,0,1),
                  (0,0):Instruction(1,1,-1)}
    demo,_ = check(demo_program,(1,1,1),12)
    assert demo.observe()[0]
    atomic_steps=verify_atomic_cell_commit()
    restart_steps,restart_sources,restart_halted = verify_fresh_restart(
        demo_program,(1,1,1),1000)
    assert restart_halted and restart_sources == 4
    looping={(0,0):Instruction(0,0,0)}
    loop_steps,loop_sources,loop_halted=verify_fresh_restart(looping,(),200)
    assert not loop_halted and loop_sources > 0
    rng=random.Random(20261027)
    snapshots=0
    for _ in range(100):
        program={}
        for state in range(3):
            for bit in (0,1):
                if rng.randrange(5):
                    program[state,bit]=Instruction(rng.randrange(3),
                                                   rng.randrange(2),
                                                   rng.choice((-1,0,1)))
        word=tuple(rng.randrange(2) for _ in range(rng.randrange(5)))
        _,count=check(program,word,10)
        snapshots+=count
    print(json.dumps({'demo_halt':demo.observe()[0],
                      'demo_native_contractions':demo.trie.steps,
                      'random_programs':100,
                      'checked_source_boundaries':snapshots,
                      'atomic_commit_native_steps_checked':atomic_steps,
                      'fresh_restart_native_steps':restart_steps,
                      'fresh_restart_source_steps':restart_sources,
                      'stuttering_restart_native_steps':loop_steps,
                      'stuttering_restart_source_steps':loop_sources,
                      'persistent_source_control_required_between_boundaries':False,
                      'native_step_reset_implemented':True,
                      'finite_state_walker_implemented':False},indent=2))


if __name__=='__main__':
    main()
