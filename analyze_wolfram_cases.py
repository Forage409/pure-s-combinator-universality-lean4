"""
Analyze the 12 non-halting S-combinator evolutions highlighted by Stephen Wolfram,
plus all non-halting terms of size 7 and 8.
"""

from s_engine import DAGPool, enumerate_trees_by_size

WOLFRAM_12 = [
    "s[s[s[s[s]][s]]][s][s]",
    "s[s][s][s[s[s]]][s[s]]",
    "s[s][s][s[s[s[s][s]]]][s]",
    "s[s[s[s]][s[s[s]][s]]][s][s]",
    "s[s][s][s][s][s][s[s[s]]][s]",
    "s[s][s][s[s[s[s][s]][s]]][s]",
    "s[s[s][s][s[s]]][s[s][s]][s]",
    "s[s][s][s[s[s]]][s[s]][s[s]",  # fix bracket below
    "s[s][s][s][s[s][s]][s][s][s][s]",
    "s[s][s][s[s[s[s[s]][s]][s]]][s]",
    "s[s][s][s[s][s[s[s[s][s]]]]][s]",
    "s[s[s[s]][s][s]][s[s[s]][s]][s]",
]
WOLFRAM_12[7] = "s[s][s][s[s[s]]][s[s]][s[s]]"


def analyze_evolution(pool: DAGPool, expr_str: str, steps: int = 200) -> None:
    node = pool.parse(expr_str)
    init_str = pool.to_str(node)
    cur = node
    leaf_counts = [pool.leaf_count(cur)]
    depths = [pool.depth(cur)]
    spine_lens = [len(pool.spine(cur))]
    head_only = True

    for t in range(steps):
        # Check if leftmost-outermost step is a head step
        sp = pool.spine(cur)
        if len(sp) < 3:
            head_only = False
        nxt, changed = pool.step_leftmost_outermost(cur)
        if not changed:
            print(f"{init_str}: HALTED at step {t}")
            return
        cur = nxt
        leaf_counts.append(pool.leaf_count(cur))
        depths.append(pool.depth(cur))
        spine_lens.append(len(pool.spine(cur)))

    diffs = [leaf_counts[i + 1] - leaf_counts[i] for i in range(len(leaf_counts) - 1)]
    print(f"=== {init_str} (size {leaf_counts[0]}) ===")
    print(f"  Purely head-reductions for {steps} steps? {head_only}")
    print(f"  Leaf count @ {steps}: {leaf_counts[-1]} (log2 ~ {leaf_counts[-1].bit_length()})")
    print(f"  Depth @ {steps}: {depths[-1]}, Spine len range: [{min(spine_lens)}, {max(spine_lens)}]")
    print(f"  First 30 leaf-count diffs: {diffs[:30]}")
    print(f"  First 30 spine lengths:    {spine_lens[:30]}")


if __name__ == "__main__":
    pool = DAGPool()
    analyze_evolution(pool, "SSS(SS)SS", 200)
    for w in WOLFRAM_12:
        analyze_evolution(pool, w, 200)
