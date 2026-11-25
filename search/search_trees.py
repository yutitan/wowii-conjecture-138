#!/usr/bin/env python3
"""
Exhaustive search for counterexamples to Written on the Wall II conjecture #138
among trees.

Requires nauty (https://pallini.di.uniroma1.it/).  On Debian/Ubuntu the
binaries are installed by

    sudo apt install nauty

under the names "geng" (upstream) or "nauty-geng" (Debian).

The script generates all unlabeled trees on n vertices with

    geng -c -q n n-1:n-1

(graphs that are connected and have n-1 edges are exactly the trees on n
vertices), analyses each tree, and reports the trees that violate

    path(G) >= (2 + u(G)) * dist_min(M(G^2)).

For trees:
  * path(G) is diameter(G) + 1 (a longest path in a tree is induced);
  * u(G) is computed by a tree DP that counts maximum independent sets,
    capped at 2 (only uniqueness matters);
  * M(G^2) and dist_min are computed from the square graph directly.

The DP and the path computation are cross-checked against brute force with
--verify (all trees with n <= 10).

Usage:
    python3 search_trees.py                  # all trees with n <= 18
    python3 search_trees.py --max-n 18
    python3 search_trees.py --max-n 10 --verify

Recorded output (n <= 18): results.txt
"""

import argparse
import shutil
import subprocess
import sys
from collections import deque

# Number of unlabeled trees on n vertices (OEIS A000055), used as a sanity check.
TREE_COUNTS = {
    1: 1, 2: 1, 3: 1, 4: 2, 5: 3, 6: 6, 7: 11, 8: 23, 9: 47, 10: 106,
    11: 235, 12: 551, 13: 1301, 14: 3159, 15: 7741, 16: 19320, 17: 48629,
    18: 123867,
}


def find_geng():
    for name in ("geng", "nauty-geng"):
        path = shutil.which(name)
        if path:
            return path
    sys.exit(
        "error: geng not found. Install nauty (e.g. 'sudo apt install nauty') "
        "or put geng on your PATH."
    )


def parse_graph6(s):
    """Decode a graph6 string into an adjacency list of sets."""
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        x = ord(ch) - 63
        bits.extend([(x >> 5) & 1, (x >> 4) & 1, (x >> 3) & 1,
                     (x >> 2) & 1, (x >> 1) & 1, x & 1])
    adj = [set() for _ in range(n)]
    k = 0
    for i in range(1, n):
        for j in range(i):
            if bits[k]:
                adj[i].add(j)
                adj[j].add(i)
            k += 1
    return adj


def bfs(adj, source):
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


def count_max_independent_sets(adj):
    """Tree DP for (alpha, number of maximum independent sets, capped at 2)."""
    n = len(adj)
    parent = [-1] * n
    parent[0] = -2
    order = [0]
    for v in order:
        for w in adj[v]:
            if parent[w] == -1:
                parent[w] = v
                order.append(w)
    dp0 = [None] * n  # v not chosen
    dp1 = [None] * n  # v chosen
    for v in reversed(order):
        size0, count0 = 0, 1
        size1, count1 = 1, 1
        for w in adj[v]:
            if parent[w] != v:
                continue
            a, b = dp0[w]
            c, d = dp1[w]
            if a > c:
                size0 += a
                count0 = min(2, count0 * b)
            elif c > a:
                size0 += c
                count0 = min(2, count0 * d)
            else:
                size0 += a
                count0 = min(2, count0 * (b + d))
            size1 += a
            count1 = min(2, count1 * b)
        dp0[v] = (size0, count0)
        dp1[v] = (size1, count1)
    a, b = dp0[0]
    c, d = dp1[0]
    if a > c:
        return a, b
    if c > a:
        return c, d
    return a, min(2, b + d)


def analyse(adj):
    """Return the quantities of conjecture #138, or None if |M(G^2)| < 2."""
    n = len(adj)
    dist = [bfs(adj, v) for v in range(n)]
    diameter = max(max(row) for row in dist)
    path = diameter + 1  # G is a tree: its longest path is induced

    square = [set() for _ in range(n)]
    for u in range(n):
        for v in range(n):
            if u != v and dist[u][v] <= 2:
                square[u].add(v)

    degree2 = [len(s) for s in square]
    max_degree = max(degree2)
    M = [v for v in range(n) if degree2[v] == max_degree]
    if len(M) < 2:
        # dist_min(M(G^2)) is undefined (or 0): no counterexample can occur.
        return None

    square_dist = [bfs(square, v) for v in M]
    dist_min = min(
        square_dist[i][M[j]] for i in range(len(M)) for j in range(i + 1, len(M))
    )

    alpha, n_max_sets = count_max_independent_sets(adj)
    u = 1 if n_max_sets == 1 else 0
    rhs = (2 + u) * dist_min
    return {
        "path": path,
        "u": u,
        "alpha": alpha,
        "M": M,
        "dist_min": dist_min,
        "rhs": rhs,
        "gap": rhs - path,
    }


# ------------------------------------------------------- brute-force checks

def brute_max_independent_sets(adj):
    n = len(adj)
    best, count = -1, 0

    def rec(v, chosen):
        nonlocal best, count
        if v == n:
            k = len(chosen)
            if k > best:
                best, count = k, 1
            elif k == best:
                count += 1
            return
        rec(v + 1, chosen)
        if not (adj[v] & chosen):
            chosen.add(v)
            rec(v + 1, chosen)
            chosen.remove(v)

    rec(0, set())
    return best, count


def brute_longest_induced_path(adj):
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

    for start in range(len(adj)):
        extend([start], {start})
    return best


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=18,
                        help="largest number of vertices (default: 18)")
    parser.add_argument("--verify", action="store_true",
                        help="cross-check DP and path values against brute force "
                             "for all trees with n <= 10")
    args = parser.parse_args()

    geng = find_geng()
    total = 0
    all_counterexamples = []

    for n in range(3, args.max_n + 1):
        out = subprocess.run(
            [geng, "-c", "-q", str(n), "%d:%d" % (n - 1, n - 1)],
            capture_output=True, text=True, check=True,
        ).stdout
        graph6 = [s for s in out.split() if s and not s.startswith(">")]
        expected = TREE_COUNTS.get(n)
        if expected is not None and len(graph6) != expected:
            sys.exit("error: geng returned %d trees on %d vertices, expected %d"
                     % (len(graph6), n, expected))

        counterexamples = []
        for g6 in graph6:
            adj = parse_graph6(g6)
            if args.verify and n <= 10:
                alpha, nsets = brute_max_independent_sets(adj)
                u_brute = 1 if nsets == 1 else 0
                path_brute = len(brute_longest_induced_path(adj))
                alpha_dp, nsets_dp = count_max_independent_sets(adj)
                u_dp = 1 if nsets_dp == 1 else 0
                diameter = max(max(row) for row in [bfs(adj, v) for v in range(n)])
                assert (alpha, u_brute) == (alpha_dp, u_dp), g6
                assert path_brute == diameter + 1, g6
            r = analyse(adj)
            if r is not None and r["gap"] > 0:
                counterexamples.append((g6, r))

        total += len(graph6)
        all_counterexamples.extend((n, g6, r) for g6, r in counterexamples)
        print("n = %2d: %6d trees, %d counterexample(s)" %
              (n, len(graph6), len(counterexamples)), flush=True)
        for g6, r in counterexamples:
            print("        %s  path=%d u=%d M=%s dist_min=%d RHS=%d"
                  % (g6, r["path"], r["u"], r["M"], r["dist_min"], r["rhs"]),
                  flush=True)

    print()
    print("total trees checked: %d" % total)
    print("total counterexamples: %d" % len(all_counterexamples))
    if total == sum(TREE_COUNTS[n] for n in range(3, args.max_n + 1)):
        print("tree counts agree with OEIS A000055")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
