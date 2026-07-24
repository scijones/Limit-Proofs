"""
Money-plot experiments for the treewidth behavioral-ceiling paper.

Three panels, each tied to a specific claim in the text:

Panel A  (Belief-revision cost vs. interaction width)
    The Sokoban-shaped time-expanded CSP from the worked example
    (ex:sokoban): per time slice, the w boxes that share a room form a
    clique (collision + arbitrary pairwise relations); consecutive
    slices are linked by movement (push-dynamics) relations.  The
    constraint graph per room is exactly the Cartesian product
    P_T x K_w, whose treewidth is w -- so the structure knob IS
    treewidth, exactly, by construction.  A solution is planted
    (consistent belief state), one late-time variable is pinned to a
    contradicting observed value (Definition def:pinned), and a
    standard generic solver (backtracking + forward checking + MRV)
    re-solves.  Cost = search nodes.  Size n = m*T is varied
    independently of w.

Panel B  (FPT collapse and the width-exploiting contrast)
    Same data.  Fit cost ~ a * n^c on the w=1 rows, then plot
    cost / n^c against w.  Overlay: a width-EXPLOITING solver
    (frontier DP over the temporal decomposition; bucket elimination)
    run on the SAME instances, verdict-cross-checked against search.
    Its measured cost is f(w) * n by construction; generic search
    matches the FPT form only sub-critically and departs upward at
    the phase transition.  Together they bracket the claim: bounded
    width makes revision tractable, and the bound must be exploited.

Panel C  (Capacity-demand matching law)
    Environments demand coordination width d: episodes of matched
    open/close pairs whose intervals overlap (cross-serially) up to
    depth d -- the canonical pattern requiring MCFG dimension ~d, and
    whose time-ordered constraint structure has pathwidth ~d.  An
    online serial agent with frontier capacity kappa (exact joint
    certificate over at most kappa open coordinates; mini-bucket /
    MBE(i=kappa) frontier propagation, Dechter & Rish 2003) is run
    across d = 1..8 for several kappa.  Prediction from the theorems:
    behaviorally achieved coordination width W_eff = min(d, kappa).
    Curves track the identity line, then knee at kappa.  Lucky
    1/|D| guesses soften the cliff into a knee.

Panel D  (Capacity saturation)
    Same machinery, transposed: success rate vs. kappa at fixed
    demands d.  Success saturates exactly at kappa = d; increasing
    internal capacity beyond the environment's demand buys nothing.

Panel E  (Emergent capacity from ordinary learning machinery)
    Sokoban levels matching the paper's worked example.  Demand d =
    number of boxes whose trajectories must be jointly coordinated
    (independent corridors d=1; two crossing d=2; three reversed d=3;
    same grid budget, all BFS-verified solvable).  Learner: standard
    linear Q-learning over indicator features on object cliques of
    order <= k (factored RL / coordination graphs, Guestrin et al.).
    The learner's effective coordination width is a CONSEQUENCE of
    its feature basis -- parameters and structure, not an explicit
    frontier buffer.  Prediction: the feature order required for
    success tracks demand, and capacity above demand buys nothing.

Usage:
    python treewidth_money_plot.py            # full run
    python treewidth_money_plot.py --quick    # reduced budgets
    python treewidth_money_plot.py --smoke    # seconds; sanity check
    python treewidth_money_plot.py --skip-cap --skip-rl --skip-csp

Dependencies: numpy, matplotlib.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import random
import sys
from collections import defaultdict

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

sys.setrecursionlimit(50_000)

HERE = os.path.dirname(os.path.abspath(__file__))


# =====================================================================
# Panel A/B: Sokoban-shaped time-expanded CSP  (P_T x K_w per room)
# =====================================================================

class Budget(Exception):
    pass


def build_room(w: int, T: int, c: int, p: float, rng: random.Random):
    """One room: w boxes over T time slices, domain = c cells.

    Constraint graph = P_T x K_w  (treewidth exactly w for T >= 2).
      - slice cliques: collision (x != y) + random forbidden pairs with
        tightness p ("arbitrary relations", the paper's premise), with
        a planted solution always kept allowed;
      - inter-slice matching: movement relation |delta| <= 1 (cyclic).

    Returns (N, domains, adj, planted) with variables indexed
    vid = box * T + t, domains as bitmasks over c values.
    """
    N = w * T
    vid = lambda j, t: j * T + t
    full = (1 << c) - 1

    # Planted belief state: distinct constant positions per box.
    cells = rng.sample(range(c), w)
    planted = [0] * N
    for j in range(w):
        for t in range(T):
            planted[vid(j, t)] = cells[j]

    adj: list[list] = [[] for _ in range(N)]

    def add(u: int, v: int, rel_uv: list[int]) -> None:
        rel_vu = [0] * c
        for a in range(c):
            m = rel_uv[a]
            b = 0
            while m:
                if m & 1:
                    rel_vu[b] |= 1 << a
                m >>= 1
                b += 1
        adj[u].append((v, rel_uv))
        adj[v].append((u, rel_vu))

    # Movement (push dynamics): position changes by at most 1 per step.
    move = [0] * c
    for a in range(c):
        for d in (-1, 0, 1):
            move[a] |= 1 << ((a + d) % c)
    for j in range(w):
        for t in range(T - 1):
            add(vid(j, t), vid(j, t + 1), move)

    # Slice cliques: collision + arbitrary (random, tightness p) relations.
    for t in range(T):
        for x in range(w):
            for y in range(x + 1, w):
                u, v = vid(x, t), vid(y, t)
                pu, pv = planted[u], planted[v]
                rel = []
                for a in range(c):
                    mask = 0
                    for b in range(c):
                        if a == b:
                            continue  # collision
                        if a == pu and b == pv:
                            mask |= 1 << b  # planted stays allowed
                            continue
                        if rng.random() < p:
                            continue  # random forbid
                        mask |= 1 << b
                    rel.append(mask)
                add(u, v, rel)

    # Sanity: planted satisfies everything.
    for u in range(N):
        for (v, rel) in adj[u]:
            assert rel[planted[u]] >> planted[v] & 1, "planted violated"

    return N, [full] * N, adj, planted


def solve(N: int, domains: list[int], adj: list[list], node_cap: int):
    """Generic backtracking search with forward checking and MRV.

    Returns (sat: bool, nodes: int).  Raises Budget past node_cap.
    Node = one value assignment attempt (standard count).
    """
    dom = list(domains)
    assigned = [False] * N
    trail: list = []
    state = {"nodes": 0}

    def propagate(u: int, a: int) -> bool:
        for (v, rel) in adj[u]:
            if assigned[v]:
                continue
            nd = dom[v] & rel[a]
            if nd != dom[v]:
                trail.append((v, dom[v]))
                dom[v] = nd
                if nd == 0:
                    return False
        return True

    def search() -> bool:
        best, best_k = -1, 1 << 30
        for v in range(N):
            if not assigned[v]:
                k = bin(dom[v]).count("1")
                if k < best_k:
                    best, best_k = v, k
                    if k == 1:
                        break
        if best == -1:
            return True
        v = best
        vals = dom[v]
        while vals:
            a = (vals & -vals).bit_length() - 1
            vals &= vals - 1
            state["nodes"] += 1
            if state["nodes"] > node_cap:
                raise Budget()
            mark = len(trail)
            trail.append((v, dom[v]))
            dom[v] = 1 << a
            assigned[v] = True
            ok = propagate(v, a) and search()
            assigned[v] = False
            while len(trail) > mark:
                u, old = trail.pop()
                dom[u] = old
            if ok:
                return True
        return False

    sat = search()
    return sat, state["nodes"]


def build_instance(m: int, w: int, T: int, c: int, p: float, seed: int):
    """Build the full m-box instance: R = m//w independent rooms, with
    the invalidating revision applied to room 0 (observation pins box
    0's final slice to a contradicting value AND discredits its entire
    believed trajectory).  Deterministic in seed; shared by both
    solvers so they decide identical instances.

    Returns list of (N, doms, adj, planted).
    """
    rng = random.Random(seed)
    rooms = []
    for r in range(m // w):
        N, doms, adj, planted = build_room(w, T, c, p, rng)
        if r == 0:
            doms = list(doms)
            for t in range(T):
                doms[t] &= ~(1 << planted[t])
            pv = (planted[T - 1] + c // 2) % c
            doms[T - 1] = 1 << pv
        rooms.append((N, doms, adj, planted))
    return rooms


def revision_cost(rooms, node_cap: int):
    """Generic-search cost to decide all rooms (search nodes).

    Returns (nodes, censored, sat_room0).
    """
    total = 0
    censored = False
    sat0 = None
    for r, (N, doms, adj, planted) in enumerate(rooms):
        try:
            sat, nodes = solve(N, doms, adj, node_cap - total)
            total += nodes
            if r == 0:
                sat0 = sat
        except Budget:
            total = node_cap
            censored = True
            break
    return total, censored, sat0


def be_cost(rooms, w: int, T: int, c: int):
    """Width-exploiting solver: frontier DP over the temporal
    decomposition (bucket elimination).  Slice validity tables are
    dense boolean arrays over |D|^w; inter-slice movement is separable
    per box (cyclic +-1), applied as axis-wise dilation.  Cost metric:
    array cells touched -- Theta(T * w * |D|^w) per room, i.e. the
    junction-tree bound, achieved by running, not asserted.

    Returns (cells, sat_room0).
    """
    cells = 0
    sat0 = None
    for ridx, (N, doms, adj, planted) in enumerate(rooms):
        vid = lambda j, t: j * T + t
        reach = None
        sat_room = True
        for t in range(T):
            valid = np.ones((c,) * w, dtype=bool)
            # unary
            for j in range(w):
                mask = doms[vid(j, t)]
                u = np.array([(mask >> a) & 1 for a in range(c)], dtype=bool)
                shape = [1] * w
                shape[j] = c
                valid &= u.reshape(shape)
                cells += valid.size
            # intra-slice pairwise relations
            for x in range(w):
                u = vid(x, t)
                for (v, rel) in adj[u]:
                    j2, t2 = divmod(v, T)
                    if t2 == t and j2 > x:
                        R = np.array([[(rel[a] >> b) & 1 for b in range(c)]
                                      for a in range(c)], dtype=bool)
                        shape = [c if i in (x, j2) else 1 for i in range(w)]
                        valid &= R.reshape(shape)
                        cells += valid.size
            if t == 0:
                reach = valid
            else:
                # movement: each box moves by at most 1 (cyclic)
                d = reach
                for ax in range(w):
                    d = d | np.roll(d, 1, axis=ax) | np.roll(d, -1, axis=ax)
                    cells += 3 * d.size
                reach = d & valid
                cells += reach.size
            if not reach.any():
                sat_room = False
                break
        if ridx == 0:
            sat0 = sat_room
    return cells, sat0


def run_csp_experiment(widths, Ts, m, c, p_grid, seeds, node_cap, log):
    """Sweep (T, w, p, seed).  For each (T, w) the reported cost is the
    PEAK over p of the median cost -- i.e. worst case over relation
    tightness.  This matches the theorem's quantifier: tractable
    belief revision must hold for ALL choices of constraint relations
    on the hypergraph, so the structure's cost is its worst relation
    regime (empirically, the SAT/UNSAT phase transition).

    The width-exploiting solver (be_cost) is run on the same peak-p
    instances; its SAT verdict is cross-checked against search
    wherever search finished within budget.
    """
    results = {"widths": widths, "Ts": Ts, "m": m, "c": c,
               "p_grid": list(p_grid), "node_cap": node_cap, "runs": {}}
    for T in Ts:
        for w in widths:
            key = f"T{T}_w{w}"
            by_p = {}
            for p in p_grid:
                rows = []
                for s in range(seeds):
                    rooms = build_instance(m, w, T, c, p,
                                           seed=1000 * T + 10 * w + s)
                    nodes, cens, sat0 = revision_cost(rooms, node_cap)
                    rows.append({"nodes": nodes, "censored": cens,
                                 "sat": sat0})
                med = float(np.median([r["nodes"] for r in rows]))
                by_p[str(p)] = {
                    "median": med,
                    "censored_frac": sum(r["censored"] for r in rows) / len(rows),
                    "sat_frac": (sum(1 for r in rows if r["sat"])
                                 / max(sum(1 for r in rows if r["sat"] is not None), 1)),
                    "sats": [r["sat"] for r in rows],
                }
            peak_p = max(by_p, key=lambda k_: by_p[k_]["median"])
            peak = by_p[peak_p]
            # width-exploiting solver on the same peak-p instances
            be_cells_list, agree = [], True
            for s in range(seeds):
                rooms = build_instance(m, w, T, c, float(peak_p),
                                       seed=1000 * T + 10 * w + s)
                cells, be_sat = be_cost(rooms, w, T, c)
                be_cells_list.append(cells)
                gen_sat = peak["sats"][s]
                if gen_sat is not None and gen_sat != be_sat:
                    agree = False
            be_med = float(np.median(be_cells_list))
            results["runs"][key] = {"by_p": by_p, "peak_p": float(peak_p),
                                    "median": peak["median"],
                                    "censored_frac": peak["censored_frac"],
                                    "sat_frac": peak["sat_frac"],
                                    "be_median": be_med,
                                    "be_verdicts_agree": agree}
            log(f"  n={m*T:4d}  w={w}  peak nodes={peak['median']:>12.0f}"
                f"  at p={peak_p}  censored={peak['censored_frac']:.0%}"
                f"  sat={peak['sat_frac']:.0%}  BE cells={be_med:.0f}"
                f"  verdicts {'OK' if agree else 'MISMATCH!'}")
    return results


# =====================================================================
# Panels C/D: capacity-vs-demand matching for an online serial agent
# =====================================================================
#
# Environment demand d: an episode is a sequence of open/close events
# for matched pairs; the layout keeps at most d pairs open at once and
# frequently attains depth d, with pairs closed in RANDOM order (mixing
# nesting and crossing).  Crossing matched dependencies are the
# canonical cross-serial pattern: a structure interleaving d matched
# pairs requires MCFG dimension ~d (it is the w-copy / respectively-
# construction pattern), and the time-ordered constraint graph (path +
# matching) has pathwidth ~d, since a cut at a deep moment crosses d
# open matching edges.  A pair's *coordination demand* is the maximum
# number of simultaneously open pairs while it is open.
#
# Environment semantics: each pair j has a secret random bijection
# sigma_j on the value domain D.  At j's opener the agent commits a
# value v_j; at j's closer, self-consistent behavior requires emitting
# sigma_j(v_j).  Carrying that commitment across the intervening opens
# and closes is exactly the frontier-certificate obligation of the
# paper's topology remark.
#
# Agent capacity kappa: the agent processes events serially, carrying
# an exact joint certificate over at most kappa open coordinates
# (bounded-width frontier propagation == mini-bucket elimination with
# i-bound kappa on the temporal path decomposition, Dechter & Rish
# 2003, JACM).  When the frontier exceeds kappa the oldest open
# coordinate is demoted to marginal information -- the width-kappa
# projection.  kappa = None is the exact (unbounded) control.
#
# Prediction:  W_eff = min(d, kappa)  -- a matching law.  Note the
# guarantee is one-sided in the theorems (capacity ceils behavior);
# attainment of the ceiling is a property of this environment family
# (every width is exercised), which is why the identity segment shows.


def gen_episode(n_pairs: int, d: int, q: int, rng: random.Random):
    """Random open/close layout, overlap capped at (and attaining) d.

    Returns (events, demand, sigmas):
      events: list of ("open"|"close", pair_id)
      demand: pair_id -> max co-open count while open (1..d)
      sigmas: pair_id -> random bijection (list of length q)
    """
    events: list = []
    open_ids: list[int] = []
    demand: dict[int, int] = {}
    next_id, closed = 0, 0
    while closed < n_pairs:
        can_open = next_id < n_pairs and len(open_ids) < d
        can_close = len(open_ids) > 0
        if can_open and (not can_close or rng.random() < 0.55):
            i = next_id
            next_id += 1
            open_ids.append(i)
            k = len(open_ids)
            demand[i] = k
            for j in open_ids:  # co-open count grew for everyone open
                if demand[j] < k:
                    demand[j] = k
            events.append(("open", i))
        else:
            j = open_ids.pop(rng.randrange(len(open_ids)))
            events.append(("close", j))
            closed += 1
    sigmas = {i: rng.sample(range(q), q) for i in range(n_pairs)}
    return events, demand, sigmas


def run_bounded_agent(events, sigmas, q: int, kappa, rng: random.Random):
    """Serial pass with frontier capacity kappa.  Returns
    pair_id -> bool (closer emission matched sigma(opener value))."""
    window: list[int] = []          # open pair ids, oldest first
    values: dict[int, int] = {}     # joint certificate content
    truth: dict[int, int] = {}      # ground truth (experimenter's copy)
    correct: dict[int, bool] = {}
    for ev, i in events:
        if ev == "open":
            v = rng.randrange(q)
            truth[i] = v
            window.append(i)
            values[i] = v
            if kappa is not None and len(window) > kappa:
                old = window.pop(0)          # demote oldest to marginal
                del values[old]
        else:
            sig = sigmas[i]
            if i in values:                  # exact joint recall
                emit = sig[values.pop(i)]
                window.remove(i)
            else:                            # marginal only: guess
                emit = rng.randrange(q)
            correct[i] = emit == sig[truth[i]]
    return correct


def episode_metrics(demand, correct, d: int):
    """Per-demand-bin accuracy and effective width for one episode.

    W_eff = largest L such that cumulative accuracy over bins 1..L
    stays >= 0.9 (behavioral: measured from emissions only).
    """
    bins = defaultdict(lambda: [0, 0])
    for i, dem in demand.items():
        bins[dem][0] += correct[i]
        bins[dem][1] += 1
    acc = {}
    w_eff = 0
    for L in range(1, d + 1):
        hit, tot = bins[L]
        a = hit / tot if tot else 1.0
        acc[L] = a
        if a >= 0.9 and w_eff == L - 1:
            w_eff = L
    rate = sum(correct.values()) / max(len(correct), 1)
    return acc, w_eff, rate


def run_capacity_experiment(demands, kappas, sat_demands, sat_kappas,
                            n_pairs, q, instances, log):
    """Sweep (d, kappa) for panel C and (d*, kappa) for panel D."""
    results = {"demands": list(demands), "kappas": [k if k is not None else "inf" for k in kappas],
               "q": q, "n_pairs": n_pairs, "instances": instances,
               "curves": {}, "sat": {}}

    def key(k):
        return "inf" if k is None else str(k)

    for kappa in kappas:
        means, los, his = [], [], []
        for d in demands:
            ws = []
            for s in range(instances):
                rng = random.Random(7_000_000 + 97 * d + 13 * (0 if kappa is None else kappa) + s)
                ev, dem, sig = gen_episode(n_pairs, d, q, rng)
                cor = run_bounded_agent(ev, sig, q, kappa, rng)
                _, w_eff, _ = episode_metrics(dem, cor, d)
                ws.append(w_eff)
            ws = np.array(ws, float)
            means.append(float(ws.mean()))
            los.append(float(np.percentile(ws, 10)))
            his.append(float(np.percentile(ws, 90)))
        results["curves"][key(kappa)] = {"mean": means, "lo": los, "hi": his}
        log(f"  kappa={key(kappa):>3s}  W_eff over d={list(demands)}: "
            + ", ".join(f"{m:.2f}" for m in means))

    for d in sat_demands:
        means, los, his = [], [], []
        for kappa in sat_kappas:
            rs = []
            for s in range(instances):
                rng = random.Random(9_000_000 + 101 * d + 17 * kappa + s)
                ev, dem, sig = gen_episode(n_pairs, d, q, rng)
                cor = run_bounded_agent(ev, sig, q, kappa, rng)
                _, _, rate = episode_metrics(dem, cor, d)
                rs.append(rate)
            rs = np.array(rs, float)
            means.append(float(rs.mean()))
            los.append(float(np.percentile(rs, 10)))
            his.append(float(np.percentile(rs, 90)))
        results["sat"][str(d)] = {"kappas": list(sat_kappas), "mean": means,
                                  "lo": los, "hi": his}
        log(f"  d={d}  success over kappa={list(sat_kappas)}: "
            + ", ".join(f"{m:.2f}" for m in means))
    return results


# =====================================================================
# Panel E: Sokoban + linear Q-learning over object cliques of order k
# =====================================================================
#
# The learner is completely standard: semi-gradient Q-learning with a
# linear value function over indicator features.  The feature basis is
# all cliques of at most k objects (agent + 3 boxes): order 1 = one
# indicator per object position; order 2 adds pairwise joint
# indicators; etc.  Order 4 is fully tabular.  This is factored RL /
# coordination graphs (Guestrin et al., JAIR 2003) -- the learner sees
# the whole state; what k controls is which JOINT configurations the
# value function can distinguish.  Its effective coordination width is
# therefore a consequence of parameters and structure, not an explicit
# design knob.  Levels are BFS-verified solvable, so failures are
# attributable to representation, not level design.

from itertools import combinations


class Sokoban:
    """Labeled-box Sokoban with interior walls.  Standard mechanics."""
    ACTIONS = ((-1, 0), (1, 0), (0, 1), (0, -1))

    def __init__(self, H, W, walls, agent_start, box_starts, goals):
        self.H, self.W = H, W
        self.walls = frozenset(walls)
        self.agent_start = agent_start
        self.box_starts = tuple(box_starts)
        self.goals = tuple(goals)
        self.reset()

    def free(self, r, c):
        return 1 <= r <= self.H and 1 <= c <= self.W and (r, c) not in self.walls

    def reset(self):
        self.agent = self.agent_start
        self.boxes = list(self.box_starts)
        self._on = self._n_on_goal()
        return self.state()

    def state(self):
        return (self.agent, tuple(self.boxes))

    def set_state(self, s):
        self.agent = s[0]
        self.boxes = list(s[1])
        self._on = self._n_on_goal()

    def _n_on_goal(self):
        return sum(b == g for b, g in zip(self.boxes, self.goals))

    def step(self, a):
        dr, dc = self.ACTIONS[a]
        r, c = self.agent
        nr, nc = r + dr, c + dc
        reward = -0.01
        if self.free(nr, nc):
            if (nr, nc) in self.boxes:
                j = self.boxes.index((nr, nc))
                br, bc = nr + dr, nc + dc
                if self.free(br, bc) and (br, bc) not in self.boxes:
                    self.boxes[j] = (br, bc)
                    self.agent = (nr, nc)
            else:
                self.agent = (nr, nc)
        on = self._n_on_goal()
        reward += 0.5 * (on - self._on)
        self._on = on
        done = on == len(self.boxes)
        if done:
            reward += 10.0
        return self.state(), reward, done


def bfs_optimal(env: Sokoban, cap: int = 2_000_000):
    """Breadth-first search over joint states; returns optimal solution
    length or None.  Used only to certify levels are solvable."""
    from collections import deque
    start = env.reset()
    seen = {start}
    dq = deque([(start, 0)])
    while dq:
        s, dist = dq.popleft()
        for a in range(4):
            env.set_state(s)
            s2, _, done = env.step(a)
            if done:
                return dist + 1
            if s2 not in seen:
                seen.add(s2)
                if len(seen) > cap:
                    return None
                dq.append((s2, dist + 1))
    return None


def rl_levels():
    """Three levels, same grid budget (4 x 6, 3 boxes, goals in row 1).

    demand 1: boxes in separate corridors; trajectories independent.
    demand 2: two boxes must swap columns in a shared chamber (one
              must be parked mid-ascent to let the other clear);
              third box independent behind a wall.
    demand 3: three boxes in one open chamber, goal order reversed;
              three-way interleaved parking.
    """
    lv = {}
    lv[1] = dict(H=4, W=6, walls={(r, c) for c in (2, 4) for r in (1, 2, 3)},
                 agent=(4, 1), boxes=[(3, 1), (3, 3), (3, 5)],
                 goals=[(1, 1), (1, 3), (1, 5)])
    lv[2] = dict(H=4, W=6, walls={(r, 5) for r in (1, 2, 3)},
                 agent=(4, 1), boxes=[(3, 2), (3, 3), (3, 6)],
                 goals=[(1, 3), (1, 2), (1, 6)])
    lv[3] = dict(H=4, W=6, walls=set(),
                 agent=(4, 1), boxes=[(3, 2), (3, 3), (3, 4)],
                 goals=[(1, 4), (1, 3), (1, 2)])
    return lv


def clique_features(state, k: int):
    """Active indicator features: one per clique of <= k objects.
    Objects: 0 = agent, 1..3 = boxes.  Feature key = (object index
    tuple, their joint positions)."""
    agent, boxes = state
    objs = (agent,) + tuple(boxes)
    feats = []
    for r in range(1, k + 1):
        for idx in combinations(range(len(objs)), r):
            feats.append((idx, tuple(objs[i] for i in idx)))
    return feats


def greedy_solves_lin(env: Sokoban, wt: dict, k: int, step_cap: int) -> bool:
    s = env.reset()
    for _ in range(step_cap):
        feats = clique_features(s, k)
        qs = [sum(wt.get((f, a), 0.0) for f in feats) for a in range(4)]
        s, _, done = env.step(max(range(4), key=lambda a: qs[a]))
        if done:
            return True
    return False


def linear_q_learn(env: Sokoban, k: int, budget: int, rng: random.Random,
                   gamma=0.98, step_cap=100, eval_every=250):
    """Standard semi-gradient Q-learning, linear over clique features.
    Returns episodes until greedy policy first solves, or None."""
    wt: dict = {}
    n_feats = sum(1 for _ in clique_features(env.reset(), k))
    alpha = 0.25 / n_feats
    for ep in range(1, budget + 1):
        eps = max(0.05, 0.3 * (1 - ep / budget))
        s = env.reset()
        feats = clique_features(s, k)
        for _ in range(step_cap):
            qs = [sum(wt.get((f, a), 0.0) for f in feats) for a in range(4)]
            a = rng.randrange(4) if rng.random() < eps else \
                max(range(4), key=lambda i: qs[i])
            s2, r, done = env.step(a)
            feats2 = clique_features(s2, k)
            q2 = 0.0 if done else max(
                sum(wt.get((f, b), 0.0) for f in feats2) for b in range(4))
            delta = r + gamma * q2 - qs[a]
            for f in feats:
                wt[(f, a)] = wt.get((f, a), 0.0) + alpha * delta
            s, feats = s2, feats2
            if done:
                break
        if ep % eval_every == 0 and greedy_solves_lin(env, wt, k, step_cap):
            return ep
    return None


def run_rl_experiment(orders, seeds, budget, log):
    lv = rl_levels()
    results = {"budget": budget, "orders": list(orders),
               "demands": sorted(lv), "opt_len": {}, "runs": {}}
    for d in sorted(lv):
        c = lv[d]
        env = Sokoban(c["H"], c["W"], c["walls"], c["agent"],
                      c["boxes"], c["goals"])
        opt = bfs_optimal(env)
        assert opt is not None, f"level d={d} is not solvable -- fix layout"
        results["opt_len"][str(d)] = opt
        log(f"  level d={d}: BFS-certified solvable, optimal length {opt}")
    for d in sorted(lv):
        c = lv[d]
        for k in orders:
            eps_list = []
            for s in range(seeds):
                env = Sokoban(c["H"], c["W"], c["walls"], c["agent"],
                              c["boxes"], c["goals"])
                rng = random.Random(31_000 + 1000 * d + 100 * k + s)
                ep = linear_q_learn(env, k, budget, rng)
                eps_list.append(ep)
            solved = sum(e is not None for e in eps_list)
            med = float(np.median([e if e is not None else budget
                                   for e in eps_list]))
            results["runs"][f"d{d}_k{k}"] = {
                "episodes": eps_list, "median": med,
                "success_frac": solved / seeds}
            log(f"  d={d} k={k}: solved {solved}/{seeds}, "
                f"median episodes {med:.0f}")
    return results

def _median_censor(vals, cap):
    xs = [v if v is not None else cap for v in vals]
    return float(np.median(xs)), any(v is None for v in vals)


def make_figures(csp, cap, rl, out_prefix, log):
    # ---------------- Figure 1: structure vs. cost (A, B) ----------
    if csp is not None:
        fig, (axA, axB) = plt.subplots(1, 2, figsize=(11.5, 4.8))
        widths, Ts, m = csp["widths"], csp["Ts"], csp["m"]
        budget = csp["node_cap"]
        colors = plt.cm.viridis(np.linspace(0.15, 0.8, len(Ts)))

        # ---- Panel A ----
        ax = axA
        for T, col in zip(Ts, colors):
            n = m * T
            med = [csp["runs"][f"T{T}_w{w}"]["median"] for w in widths]
            cen = [csp["runs"][f"T{T}_w{w}"]["censored_frac"] > 0 for w in widths]
            ax.plot(widths, med, "-o", color=col, label=f"$n = {n}$")
            for w, y, c_ in zip(widths, med, cen):
                if c_:
                    ax.plot([w], [y], marker="^", ms=11, mfc="none",
                            mec=col, mew=1.6, ls="none")
        ax.axhline(budget, color="0.4", ls=":", lw=1)
        ax.text(widths[0], budget * 1.15, "search budget (censored $\\triangle$)",
                fontsize=8, color="0.35")
        ax.set_yscale("log")
        ax.set_xlabel("interaction width $w$  ($=$ treewidth, exact)")
        ax.set_ylabel("belief-revision cost, worst case over relations\n(peak median search nodes over tightness $p$)")
        ax.set_title("A.  Revision cost vs. structure,\nsize varied independently")
        ax.legend(frameon=False)
        ax.grid(alpha=0.3, which="both")

        # ---- Panel B ----
        ns = np.array([m * T for T in Ts], float)
        y1 = np.array([csp["runs"][f"T{T}_w1"]["median"] for T in Ts], float)
        c_hat, log_a = np.polyfit(np.log(ns), np.log(np.maximum(y1, 1.0)), 1)
        log(f"Fitted size exponent at w=1:  c = {c_hat:.2f}")

        ax = axB
        for T, col in zip(Ts, colors):
            n = m * T
            med = np.array([csp["runs"][f"T{T}_w{w}"]["median"] for w in widths], float)
            ax.plot(widths, med / n ** c_hat, "-o", color=col,
                    label=f"generic search, $n = {n}$")
        # Width-exploiting solver on the same instances (cells / n,
        # scaled to the generic w=1 level so shapes are comparable).
        base = np.median([csp["runs"][f"T{T}_w1"]["median"] / (m * T) ** c_hat
                          for T in Ts])
        agree_all = all(csp["runs"][f"T{T}_w{w}"].get("be_verdicts_agree", True)
                        for T in Ts for w in widths)
        for T, col in zip(Ts, colors):
            n = m * T
            be = np.array([csp["runs"][f"T{T}_w{w}"]["be_median"]
                           for w in widths], float)
            be = be / n ** c_hat
            be = be / be[0] * base
            ax.plot(widths, be, "--s", color=col, ms=4, alpha=0.8,
                    label=("width-exploiting (BE), all $n$"
                           if T == Ts[0] else None))
        ref = np.array([csp["c"] ** (w + 1) for w in widths], float)
        ref = ref / ref[0] * base
        ax.plot(widths, ref, ":", color="0.3",
                label=f"$|D|^{{\\,w+1}}$ upper-bound shape ($|D|={csp['c']}$)")
        # ETH lower-bound shape (Marx 2010): no algorithm beats
        # 2^{o(w / log w)} poly(n); plot 2^{w/log2 w} normalized at w=2.
        w_eth = [w for w in widths if w >= 2]
        eth = np.array([2.0 ** (w / np.log2(w)) if w > 1 else np.nan
                        for w in w_eth], float)
        eth = eth / eth[0] * base
        ax.plot(w_eth, eth, "-.", color="0.5",
                label="$2^{\\,w/\\log_2 w}$ ETH lower-bound shape")
        ax.set_yscale("log")
        ax.set_xlabel("interaction width $w$")
        ax.set_ylabel(f"cost $/\\; n^{{{c_hat:.2f}}}$  (BE curves rescaled)")
        ax.set_title("B.  Width-exploiting inference achieves the FPT\n"
                     "form $f(w)\\cdot n$; generic search departs at the\n"
                     f"transition  (verdicts cross-checked: "
                     f"{'all agree' if agree_all else 'MISMATCH'})")
        ax.legend(frameon=False, fontsize=8)
        ax.grid(alpha=0.3, which="both")

        fig.suptitle("Structure, not size, controls belief-revision cost",
                     y=1.04, fontsize=13)
        fig.tight_layout()
        for ext in ("png", "pdf"):
            path = f"{out_prefix}_structure.{ext}"
            fig.savefig(path, dpi=200, bbox_inches="tight")
            log(f"Wrote {path}")
        plt.close(fig)

    # ------------- Figure 2: capacity vs. demand (C, D, E) ---------
    n_panels = (cap is not None) * 2 + (rl is not None)
    if n_panels == 0:
        return
    fig, axes = plt.subplots(1, n_panels, figsize=(5.8 * n_panels, 4.8))
    axes = list(np.atleast_1d(axes))
    ai = 0

    if cap is not None:
        demands = cap["demands"]
        kap_keys = [str(k) for k in cap["kappas"]]  # "2", "4", ..., "inf"
        kap_colors = plt.cm.plasma(np.linspace(0.10, 0.75, len(kap_keys)))

        # ---- Panel C: matching law W_eff = min(d, kappa) ----
        ax = axes[ai]; ai += 1
        dd = np.array(demands, float)
        ax.plot(dd, dd, ":", color="0.35", lw=1.5, label="identity ($W=d$)")
        for kk, col in zip(kap_keys, kap_colors):
            cur = cap["curves"][kk]
            lbl = "exact ($\\kappa=\\infty$)" if kk == "inf" else f"$\\kappa = {kk}$"
            ax.plot(demands, cur["mean"], "-o", color=col, label=lbl)
            ax.fill_between(demands, cur["lo"], cur["hi"], color=col, alpha=0.15)
            if kk != "inf":
                ax.plot(demands, np.minimum(dd, float(kk)), "--", color=col,
                        lw=1.0, alpha=0.6)
        ax.set_xlabel("environment coordination demand $d$\n(cross-serial depth $\\approx$ MCFG dimension $\\approx$ pathwidth)")
        ax.set_ylabel("achieved coordination width $W_{\\mathrm{eff}}$ (behavioral)")
        ax.set_title("C.  Matching law: $W_{\\mathrm{eff}} = \\min(d, \\kappa)$\n(dashed: prediction)")
        ax.legend(frameon=False, fontsize=8)
        ax.grid(alpha=0.3)

        # ---- Panel D: capacity saturation at kappa = d ----
        ax = axes[ai]; ai += 1
        sat_ds = sorted(cap["sat"], key=int)
        sat_colors = plt.cm.viridis(np.linspace(0.15, 0.8, len(sat_ds)))
        for dstr, col in zip(sat_ds, sat_colors):
            s = cap["sat"][dstr]
            ax.plot(s["kappas"], s["mean"], "-o", color=col,
                    label=f"demand $d = {dstr}$")
            ax.fill_between(s["kappas"], s["lo"], s["hi"], color=col, alpha=0.15)
            ax.axvline(int(dstr), color=col, ls=":", lw=1.0, alpha=0.7)
        ax.set_ylim(0, 1.05)
        ax.set_xlabel("agent frontier capacity $\\kappa$")
        ax.set_ylabel("self-consistency rate (matched pairs correct)")
        ax.set_title("D.  Saturation: capacity beyond $d$\nbuys nothing (dotted: $\\kappa = d$)")
        ax.legend(frameon=False, fontsize=8)
        ax.grid(alpha=0.3)

    if rl is not None:
        # ---- Panel E: emergent capacity, linear Q over cliques ----
        ax = axes[ai]; ai += 1
        demands = rl["demands"]
        orders = rl["orders"]
        budget = rl["budget"]
        ord_colors = plt.cm.plasma(np.linspace(0.10, 0.75, len(orders)))
        for k, col in zip(orders, ord_colors):
            med = [rl["runs"][f"d{d}_k{k}"]["median"] for d in demands]
            cen = [rl["runs"][f"d{d}_k{k}"]["success_frac"] < 1.0
                   for d in demands]
            ax.plot(demands, med, "-o", color=col,
                    label=f"feature order $k = {k}$")
            for d, y, c_ in zip(demands, med, cen):
                if c_:
                    ax.plot([d], [y], marker="^", ms=11, mfc="none",
                            mec=col, mew=1.6, ls="none")
        ax.axhline(budget, color="0.4", ls=":", lw=1)
        ax.text(demands[0], budget * 1.1,
                "training budget ($\\triangle$: some seeds unsolved)",
                fontsize=8, color="0.35")
        ax.set_yscale("log")
        ax.set_xticks(demands)
        ax.set_xlabel("level coordination demand $d$\n(boxes requiring jointly sequenced trajectories)")
        ax.set_ylabel("episodes to greedy solution (median)")
        ax.set_title("E.  Emergent capacity: linear Q-learning, clique\n"
                     "features of order $k$.  Order 1 (no agent\u2013box term)\n"
                     "fails outright; above threshold, demand\u2013capacity\n"
                     "mismatch is paid in samples")
        ax.legend(frameon=False, fontsize=8)
        ax.grid(alpha=0.3, which="both")

    fig.suptitle("Achieved coordination width is capped by internal "
                 "structure \u2014 designed ($\\kappa$) or emergent ($k$)",
                 y=1.04, fontsize=13)
    fig.tight_layout()
    for ext in ("png", "pdf"):
        path = f"{out_prefix}_agents.{ext}"
        fig.savefig(path, dpi=200, bbox_inches="tight")
        log(f"Wrote {path}")
    plt.close(fig)


# =====================================================================
# Main
# =====================================================================

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true", help="reduced budgets")
    ap.add_argument("--smoke", action="store_true", help="tiny sanity run")
    ap.add_argument("--skip-cap", action="store_true")
    ap.add_argument("--skip-csp", action="store_true")
    ap.add_argument("--skip-rl", action="store_true")
    ap.add_argument("--out", default=os.path.join(HERE, "money_plot"))
    args = ap.parse_args()

    log = print

    # ----- budgets -----
    if args.smoke:
        widths, Ts, seeds, node_cap = [1, 2], [4], 2, 5_000
        p_grid = [0.30, 0.45]
        demands, kappas = [1, 2, 3], [2, None]
        sat_demands, sat_kappas = [2], [1, 2, 3]
        n_pairs, q, instances = 60, 8, 3
        rl_orders, rl_seeds, rl_budget = [1, 2], 1, 800
    elif args.quick:
        widths, Ts, seeds, node_cap = [1, 2, 3, 4], [6, 12], 5, 50_000
        p_grid = [0.25, 0.32, 0.40, 0.48, 0.56]
        demands, kappas = list(range(1, 9)), [2, 4, 6, None]
        sat_demands, sat_kappas = [3, 5, 7], list(range(1, 9))
        n_pairs, q, instances = 150, 8, 12
        rl_orders, rl_seeds, rl_budget = [1, 2, 3, 4], 2, 5_000
    else:
        widths, Ts, seeds, node_cap = [1, 2, 3, 4, 5, 6], [6, 12, 24], 9, 300_000
        p_grid = [0.16, 0.22, 0.28, 0.34, 0.40, 0.46, 0.52, 0.58]
        demands, kappas = list(range(1, 9)), [2, 4, 6, None]
        sat_demands, sat_kappas = [3, 5, 7], list(range(1, 9))
        n_pairs, q, instances = 300, 8, 40
        rl_orders, rl_seeds, rl_budget = [1, 2, 3, 4], 5, 25_000
    m, c = 12, 6

    csp = cap = rl = None

    if not args.skip_csp:
        log(f"[CSP] rooms P_T x K_w, m={m} boxes, |D|={c}, "
            f"p grid={p_grid}, seeds={seeds}, cap={node_cap}")
        csp = run_csp_experiment(widths, Ts, m, c, p_grid, seeds,
                                 node_cap, log)

    if not args.skip_cap:
        log(f"[CAP] cross-serial pairs={n_pairs}, |D|={q}, "
            f"instances={instances} per point")
        cap = run_capacity_experiment(demands, kappas, sat_demands,
                                      sat_kappas, n_pairs, q, instances, log)

    if not args.skip_rl:
        log(f"[RL] Sokoban levels d=1..3, linear Q over clique features, "
            f"orders={rl_orders}, seeds={rl_seeds}, budget={rl_budget}")
        rl = run_rl_experiment(rl_orders, rl_seeds, rl_budget, log)

    with open(f"{args.out}_results.json", "w") as fh:
        json.dump({"csp": csp, "cap": cap, "rl": rl}, fh, indent=1)
    log(f"Wrote {args.out}_results.json")

    make_figures(csp, cap, rl, args.out, log)


if __name__ == "__main__":
    main()
