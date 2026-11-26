"""
Pure S-Combinator Research & Simulation Engine
Rule: S x y z -> x z (y z)
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Dict, List, Optional, Set, Tuple


class DAGPool:
    """Hash-consed DAG representation of pure S-combinator terms."""

    def __init__(self) -> None:
        # Node 0 is always the leaf 'S'
        self.nodes: List[Optional[Tuple[int, int]]] = [None]
        self.lookup: Dict[Tuple[int, int], int] = {}
        self.size_cache: Dict[int, int] = {0: 1}
        self.depth_cache: Dict[int, int] = {0: 0}
        self.spine_cache: Dict[int, Tuple[int, ...]] = {0: ()}
        self.step_lo_cache: Dict[int, Tuple[int, bool]] = {0: (0, False)}

    @property
    def S(self) -> int:
        return 0

    def app(self, f: int, x: int) -> int:
        key = (f, x)
        res = self.lookup.get(key)
        if res is None:
            res = len(self.nodes)
            self.nodes.append(key)
            self.lookup[key] = res
        return res

    def app_many(self, head: int, args: List[int] | Tuple[int, ...]) -> int:
        cur = head
        for a in args:
            cur = self.app(cur, a)
        return cur

    def leaf_count(self, node: int) -> int:
        if node in self.size_cache:
            return self.size_cache[node]
        pair = self.nodes[node]
        assert pair is not None
        sz = self.leaf_count(pair[0]) + self.leaf_count(pair[1])
        self.size_cache[node] = sz
        return sz

    def depth(self, node: int) -> int:
        if node in self.depth_cache:
            return self.depth_cache[node]
        pair = self.nodes[node]
        assert pair is not None
        d = 1 + max(self.depth(pair[0]), self.depth(pair[1]))
        self.depth_cache[node] = d
        return d

    def spine(self, node: int) -> Tuple[int, ...]:
        """Returns the tuple of arguments (A_1, A_2, ..., A_k) such that node = S A_1 ... A_k."""
        if node in self.spine_cache:
            return self.spine_cache[node]
        args: List[int] = []
        cur = node
        while cur != 0:
            pair = self.nodes[cur]
            assert pair is not None
            args.append(pair[1])
            cur = pair[0]
        args.reverse()
        res = tuple(args)
        self.spine_cache[node] = res
        return res

    def step_head(self, node: int) -> Tuple[int, bool]:
        """Performs one head-reduction step if the spine has >= 3 arguments."""
        sp = self.spine(node)
        if len(sp) < 3:
            return node, False
        x, y, z = sp[0], sp[1], sp[2]
        xz = self.app(x, z)
        yz = self.app(y, z)
        xzyz = self.app(xz, yz)
        return self.app_many(xzyz, sp[3:]), True

    def step_leftmost_outermost(self, node: int) -> Tuple[int, bool]:
        """Performs one leftmost-outermost (normal order) reduction step."""
        if node in self.step_lo_cache:
            return self.step_lo_cache[node]
        sp = self.spine(node)
        if len(sp) >= 3:
            res, changed = self.step_head(node)
            self.step_lo_cache[node] = (res, changed)
            return res, changed
        # Otherwise spine has length 0, 1, or 2; reduce leftmost argument that can reduce
        for i, arg in enumerate(sp):
            new_arg, changed = self.step_leftmost_outermost(arg)
            if changed:
                new_sp = list(sp)
                new_sp[i] = new_arg
                res = self.app_many(0, new_sp)
                self.step_lo_cache[node] = (res, True)
                return res, True
        self.step_lo_cache[node] = (node, False)
        return node, False

    def to_str(self, node: int, is_right: bool = False) -> str:
        if node == 0:
            return "S"
        pair = self.nodes[node]
        assert pair is not None
        s = f"{self.to_str(pair[0], False)}{self.to_str(pair[1], True)}"
        return f"({s})" if is_right else s

    def parse(self, s: str) -> int:
        """Parses left-associative S-Combinator string like 'SSS(SS)SS' or 's[s][s][s[s]][s][s]'."""
        s = s.strip()
        if "[" in s:
            # Wolfram format: s[a][b]
            s = s.replace("s", "S")
            idx = 0

            def parse_wolfram() -> int:
                nonlocal idx
                assert s[idx] == "S"
                idx += 1
                cur = 0
                while idx < len(s) and s[idx] == "[":
                    idx += 1  # skip '['
                    arg = parse_wolfram()
                    assert s[idx] == "]"
                    idx += 1  # skip ']'
                    cur = self.app(cur, arg)
                return cur

            return parse_wolfram()
        else:
            idx = 0

            def parse_expr() -> int:
                nonlocal idx
                items: List[int] = []
                while idx < len(s) and s[idx] != ")":
                    if s[idx] in " \t\n":
                        idx += 1
                    elif s[idx] == "S" or s[idx] == "s":
                        items.append(0)
                        idx += 1
                    elif s[idx] == "(":
                        idx += 1
                        items.append(parse_expr())
                        assert idx < len(s) and s[idx] == ")"
                        idx += 1
                    else:
                        raise ValueError(f"Unexpected char {s[idx]} at {idx}")
                assert len(items) >= 1
                return self.app_many(items[0], items[1:])

            return parse_expr()


def enumerate_trees_by_size(pool: DAGPool, max_leaves: int) -> Dict[int, List[int]]:
    """Enumerates all pure S-trees with 1..max_leaves leaves (Catalan numbers)."""
    by_size: Dict[int, List[int]] = {1: [pool.S]}
    for n in range(2, max_leaves + 1):
        trees: List[int] = []
        for left_sz in range(1, n):
            right_sz = n - left_sz
            for l_node in by_size[left_sz]:
                for r_node in by_size[right_sz]:
                    trees.append(pool.app(l_node, r_node))
        by_size[n] = trees
    return by_size


if __name__ == "__main__":
    pool = DAGPool()
    by_size = enumerate_trees_by_size(pool, 7)
    for sz, nodes in by_size.items():
        non_halting = []
        max_steps = 0
        for nd in nodes:
            cur = nd
            for step in range(200):
                nxt, changed = pool.step_leftmost_outermost(cur)
                if not changed:
                    max_steps = max(max_steps, step)
                    break
                cur = nxt
            else:
                non_halting.append(pool.to_str(nd))
        print(f"Size {sz}: {len(nodes)} terms, max halting steps={max_steps}, non-halting={len(non_halting)}: {non_halting}")
