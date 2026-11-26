"""Decode source output from a halted Neary U(3,11) tape.

The start index is the cell under the halted U head (DELTA). The source was
compiled by normalize_neary_safe, so its logical bits are odd positions of
the marked simulated tape. Returned bits have trailing zeros trimmed.
"""
from neary_u3_11 import S


def decode_halted_output(tape,head):
    get=lambda i: tape.get(i,S['LA'])
    assert get(head)==S['DELTA']
    i=head+1
    while get(i)==S['LA']:
        i+=1
        assert i <= max(tape,default=head)+1
    first_b=i
    while get(i)==S['LB']:
        i+=1
    assert i-first_b >= 2 and get(i)==S['LA']
    i+=1
    end=max(tape,default=i)
    marked_bits=[]
    while i<=end:
        first,second=get(i),get(i+1)
        assert first in (S['LA'],S['LB']) and second==S['LA']
        marked_bits.append(int(first==S['LB']))
        i+=2
    assert marked_bits and marked_bits[0]==1
    assert all(bit==0 for bit in marked_bits[2::2])
    output=marked_bits[1::2]
    while output and not output[-1]: output.pop()
    return tuple(output)
