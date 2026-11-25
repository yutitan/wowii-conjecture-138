#!/usr/bin/env python3
"""
Verification of counterexamples to Written on the Wall II conjecture #138.

Conjecture #138 (Graffiti.pc; announced 2005-07-12; WOWII entry 138):

    If G is a simple connected graph, then
        path(G) >= (2 + u(G)) * dist_min(M(G^2)).

Definitions (WOWII definitions 35, 74, 19, 75):
  path(G)  : number of vertices of a largest induced path of G;
  u(G)     : 1 if G has a unique maximum independent set, 0 otherwise
             (definition 74 -- see README for the missing word "maximum");
  M(G^2)   : set of vertices of maximum degree of the square G^2;
  dist_min : minimum distance between distinct vertices of M(G^2),
             measured in G^2.

This script verifies, using only the Python standard library and only the edge
lists below, that each tree listed violates the inequality.

Usage:
    python3 verify.py

Python 3.10 or newer is required. Exit status is 0 if and only if every check
passes.
"""

from collections import deque
from itertools import combinations

# ---------------------------------------------------------------- data

TREES = {
    # The three (and only three) 18-vertex trees that violate the conjecture.
    # Labels are those of nauty's canonical labelling, see data/.
    "A18": [(0, 11), (0, 12), (1, 11), (1, 13), (2, 12), (2, 14), (3, 13),
            (3, 16), (4, 14), (4, 17), (5, 15), (6, 15), (7, 16), (8, 17),
            (9, 17), (10, 17), (15, 16)],
    "B18": [(0, 11), (0, 12), (1, 11), (1, 13), (2, 12), (2, 16), (3, 13),
            (3, 17), (4, 14), (5, 14), (6, 15), (6, 16), (7, 15), (8, 15),
            (9, 16), (10, 17), (14, 17)],
    "C18": [(0, 9), (0, 12), (1, 10), (1, 16), (2, 11), (2, 16), (3, 12),
            (3, 13), (4, 13), (4, 14), (5, 14), (5, 16), (6, 15), (7, 15),
            (8, 17), (9, 17), (15, 17)],
    # A 21-vertex witness (the counterexample originally written down).
    "T21": [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8),
            (8, 9), (9, 10), (10, 11), (11, 12), (0, 13), (13, 14), (0, 15),
            (15, 16), (12, 17), (17, 18), (12, 19), (19, 20)],
}

GRAPH6 = {
    "A18": "Q?????????W?g?S?D??K?COCGw?",
    "B18": "Q?????????W?g?S?@_?F?Gc?OG_",
    "C18": "Q??????_A?C?c?E?@_?E?X???oO",
    "T21": "ThCGGC@?G?_@?@_???K????C?A???G?C???@",
}

# Exact values this script asserts (computed by the script itself below).
EXPECTED = {
    "A18": dict(n=18, path=14, alpha=11, u=1, M=(4, 16), dist2=5, distG=9,
                rhs2=15, rhsG=27),
    "B18": dict(n=18, path=14, alpha=11, u=1, M=(6, 17), dist2=5, distG=9,
                rhs2=15, rhsG=27),
    "C18": dict(n=18, path=14, alpha=10, u=1, M=(16, 17), dist2=5, distG=9,
                rhs2=15, rhsG=27),
    "T21": dict(n=21, path=17, alpha=11, u=1, M=(0, 12), dist2=6, distG=12,
                rhs2=18, rhsG=36),
}


# ---------------------------------------------------------------- graph routines

def build_graph(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        assert 0 <= u < n and 0 <= v < n and u != v, (u, v)
        adj[u].add(v)
        adj[v].add(u)
    return adj


def is_tree(adj):
    n = len(adj)
    if sum(len(s) for s in adj) != 2 * (n - 1):
        return False
    seen = {0}
    stack = [0]
    while stack:
        v = stack.pop()
        for w in adj[v]:
            if w not in seen:
                seen.add(w)
                stack.append(w)
    return len(seen) == n


def distances(adj, source):
    dist = [-1] * len(adj)
    dist[source] = 0
    queue = deque([source])
    while queue:
        v = queue.popleft()
        for w in adj[v]:
            if dist[w] < 0:
                dist[w] = dist[v] + 1
                queue.append(w)
    return dist


def square_graph(adj):
    n = len(adj)
    sq = [set() for _ in range(n)]
    for v in range(n):
        for w, d in enumerate(distances(adj, v)):
            if 1 <= d <= 2:
                sq[v].add(w)
    return sq


def longest_induced_path(adj):
    """Exhaustive search. For the trees below this is fast (O(n^2) paths)."""
    n = len(adj)
    best = []

    def extend(path, used):
        nonlocal best
        if len(path) > len(best):
            best = list(path)
        last = path[-1]
        for w in adj[last]:
            if w in used:
                continue
            if any(w in adj[x] for x in path[:-1]):
                continue
            path.append(w)
            used.add(w)
            extend(path, used)
            path.pop()
            used.remove(w)

    for start in range(n):
        extend([start], {start})
    return best


def max_independent_sets(adj):
    """Exhaustively enumerate all independent sets.

    Returns (alpha, number of maximum independent sets, one of them as a bit
    mask). Enumeration is over all 2^n subsets; n <= 21 here, so this takes at
    most a few seconds.
    """
    n = len(adj)
    adjmask = [sum(1 << w for w in adj[v]) for v in range(n)]
    best = -1
    count = 0
    witness = 0

    def rec(v, chosen):
        nonlocal best, count, witness
        if v == n:
            k = chosen.bit_count()
            if k > best:
                best, count, witness = k, 1, chosen
            elif k == best:
                count += 1
            return
        rec(v + 1, chosen)              # do not take v
        if not adjmask[v] & chosen:     # take v
            rec(v + 1, chosen | (1 << v))

    rec(0, 0)
    return best, count, witness


def decode_graph6(s):
    """Decode a graph6 string into a set of unordered edges."""
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        x = ord(ch) - 63
        bits.extend([(x >> 5) & 1, (x >> 4) & 1, (x >> 3) & 1,
                     (x >> 2) & 1, (x >> 1) & 1, x & 1])
    edges = set()
    k = 0
    for i in range(1, n):
        for j in range(i):
            if bits[k]:
                edges.add((j, i))
            k += 1
    return n, edges


# ---------------------------------------------------------------- main

def main():
    print("Verifying counterexamples to Written on the Wall II conjecture #138")
    print("  path(G) >= (2 + u(G)) * dist_min(M(G^2))\n")
    fmt = "{:<5} {:>3} {:>5} {:>6} {:>2} {:>9} {:>9} {:>9} {:>9} {:>6}"
    print(fmt.format("tree", "n", "edges", "path", "u", "M(G^2)", "dist_G2",
                     "dist_G", "RHS_G2", "fails?"))
    print("-" * 72)

    failures = 0
    for name, edges in TREES.items():
        exp = EXPECTED[name]
        n = exp["n"]
        adj = build_graph(n, edges)

        # 1. Each graph is a tree (hence a connected graph).
        assert is_tree(adj), name + ": not a tree"
        assert len(edges) == n - 1

        # 2. The graph6 string encodes the same graph.
        g6_n, g6_edges = decode_graph6(GRAPH6[name])
        assert g6_n == n, name + ": graph6 vertex count"
        assert g6_edges == set(edges), name + ": graph6 does not match the edge list"

        # 3. path(G): exhaustive search over induced paths.
        path = longest_induced_path(adj)

        # 4. u(G): exhaustive enumeration of independent sets.
        alpha, n_mis, witness = max_independent_sets(adj)
        u = 1 if n_mis == 1 else 0

        # 5. M(G^2), distances.
        sq = square_graph(adj)
        deg2 = [len(s) for s in sq]
        dmax = max(deg2)
        M = tuple(v for v in range(n) if deg2[v] == dmax)
        assert len(M) >= 2, name + ": M(G^2) has fewer than two vertices"
        pairs = list(combinations(M, 2))
        dist2 = min(distances(sq, a)[b] for a, b in pairs)
        distG = min(distances(adj, a)[b] for a, b in pairs)

        rhs2 = (2 + u) * dist2
        rhsG = (2 + u) * distG
        fails = len(path) < rhs2

        # 6. Compare with the values claimed in the README.
        assert exp["path"] == len(path), (name, "path", len(path))
        assert exp["alpha"] == alpha, (name, "alpha", alpha)
        assert exp["u"] == u, (name, "u", u)
        assert exp["M"] == M, (name, "M", M)
        assert exp["dist2"] == dist2, (name, "dist2", dist2)
        assert exp["distG"] == distG, (name, "distG", distG)
        assert exp["rhs2"] == rhs2, (name, "rhs2", rhs2)
        assert exp["rhsG"] == rhsG, (name, "rhsG", rhsG)
        assert fails, name + ": the inequality is not violated"

        mis = sorted(v for v in range(n) if (witness >> v) & 1)
        print(fmt.format(name, n, len(edges), len(path), u, str(M), dist2,
                         distG, rhs2, "yes"))
        print("      path:", " ".join(map(str, path)))
        print("      alpha =", alpha, "| maximum independent set:", mis,
              "| unique:", n_mis == 1)
        print("      G^2 degrees:", deg2)
        print()
        failures += 1

    print("All", failures, "counterexamples verified: in every case")
    print("    path(G) < (2 + u(G)) * dist_min(M(G^2)).")
    print("\nNote: the inequality is violated under BOTH natural readings of")
    print("dist_min(M(G^2)) -- distances measured in G^2 (columns RHS_G2) or")
    print("in G (columns RHS_G).  See README.md for the discussion of WOWII")
    print("definition 74 (u(G)) and of the distance ambiguity.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
