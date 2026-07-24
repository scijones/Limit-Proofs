"""
Panel E' -- emergent capacity: behavioral coordination width of a
TRAINED recurrent agent, measured identically to the designed-frontier
agent of panels C/D.

Task (same family as panels C/D): episodes of matched open/close
events with cross-serial overlap up to demand d.  At an opener the
input presents a value v in D (|D| = q); at the matching closer the
agent must emit sigma(v) for a fixed public permutation sigma.  Pairs
are identified by a reusable slot id (at most d_max concurrently
open), so carrying the open commitments across intervening events is
exactly the frontier-certificate obligation: coordination width d
requires holding d domain values simultaneously through the recurrent
bottleneck.

Agent: an ordinary GRU (hidden size h) + linear head, trained with
Adam/cross-entropy on episodes of mixed demand.  NOBODY designs a
frontier: capacity is an emergent function of parameters and training.

Measurement: purely behavioral, identical to panel C -- emissions are
binned by the demand of each pair (max co-open while open) and
W_eff = largest L such that cumulative accuracy over bins 1..L stays
>= 0.9.  The metric never looks inside the network.

Predictions (parameter-free, falsifiable):
  1. Each h-curve tracks the identity line, then plateaus (knee, not
     cliff -- 1/q lucky guesses and partial retention soften it).
  2. The plateau level increases with h.
  3. Saturation: at fixed test demand d*, performance stops improving
     once emergent capacity reaches d* -- capacity beyond demand buys
     nothing (the trained analogue of panel D).

Usage:
    python emergent_capacity.py            # full run
    python emergent_capacity.py --quick
    python emergent_capacity.py --smoke

Dependencies: numpy, matplotlib, torch (+ the task generator from
treewidth_money_plot.py in this directory).
"""
from __future__ import annotations

import argparse
import json
import os
import random
import sys

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import torch
import torch.nn as nn

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from treewidth_money_plot import gen_episode, episode_metrics  # noqa: E402

D_MAX = 8      # maximum coordination demand (and slot pool size)
Q = 8          # value domain size |D|
N_PAIRS = 30   # pairs per episode -> 60 events


def make_sigma(rng: random.Random):
    sig = list(range(Q))
    rng.shuffle(sig)
    return sig


def encode_episode(d: int, sigma, rng: random.Random):
    """One episode at demand cap d -> (inputs, targets, demand, closes).

    inputs : [T, 2 + D_MAX + Q]  one-hot (event type, slot id, value)
    targets: [T]  class in 0..Q-1 at closers, -100 elsewhere
    demand : pair id -> coordination demand (from gen_episode)
    closes : list of (timestep, pair_id) for behavioral scoring
    """
    events, demand, _ = gen_episode(N_PAIRS, d, Q, rng)
    T = len(events)
    x = np.zeros((T, 2 + D_MAX + Q), dtype=np.float32)
    y = np.full(T, -100, dtype=np.int64)
    closes = []
    slot_of, free = {}, list(range(D_MAX))
    value_of = {}
    for t, (ev, i) in enumerate(events):
        if ev == "open":
            s = free.pop(0)
            slot_of[i] = s
            v = rng.randrange(Q)
            value_of[i] = v
            x[t, 0] = 1.0
            x[t, 2 + s] = 1.0
            x[t, 2 + D_MAX + v] = 1.0
        else:
            s = slot_of.pop(i)
            free.insert(0, s)
            x[t, 1] = 1.0
            x[t, 2 + s] = 1.0
            y[t] = sigma[value_of.pop(i)]
            closes.append((t, i))
    return x, y, demand, closes


class GRUAgent(nn.Module):
    def __init__(self, h: int):
        super().__init__()
        self.gru = nn.GRU(2 + D_MAX + Q, h, batch_first=True)
        self.head = nn.Linear(h, Q)

    def forward(self, x):
        out, _ = self.gru(x)
        return self.head(out)


def train_agent(h: int, steps: int, batch: int, device, seed: int, log):
    torch.manual_seed(seed)
    rng = random.Random(seed)
    sigma = make_sigma(random.Random(12345))  # fixed public sigma
    model = GRUAgent(h).to(device)
    opt = torch.optim.Adam(model.parameters(), lr=3e-3)
    sched = torch.optim.lr_scheduler.CosineAnnealingLR(opt, T_max=steps,
                                                       eta_min=1e-4)
    lossf = nn.CrossEntropyLoss(ignore_index=-100)
    for step in range(1, steps + 1):
        # Curriculum: ramp the demand cap from 2 to D_MAX over the
        # first half of training, then mixed demand.  Low-demand
        # episodes remain in the mix throughout so bin-1 competence
        # is never forgotten.
        frac = min(1.0, 2.0 * step / steps)
        cap_d = max(2, int(round(2 + frac * (D_MAX - 2))))
        xs, ys = [], []
        for _ in range(batch):
            d = rng.randint(1, cap_d)
            x, y, _, _ = encode_episode(d, sigma, rng)
            xs.append(x)
            ys.append(y)
        # pad to common length
        L = max(x.shape[0] for x in xs)
        xb = np.zeros((batch, L, xs[0].shape[1]), dtype=np.float32)
        yb = np.full((batch, L), -100, dtype=np.int64)
        for b, (x, y) in enumerate(zip(xs, ys)):
            xb[b, :x.shape[0]] = x
            yb[b, :y.shape[0]] = y
        xb = torch.from_numpy(xb).to(device)
        yb = torch.from_numpy(yb).to(device)
        logits = model(xb)
        loss = lossf(logits.reshape(-1, Q), yb.reshape(-1))
        opt.zero_grad()
        loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
        opt.step()
        sched.step()
        if step % max(steps // 5, 1) == 0:
            log(f"    h={h} step {step}/{steps} loss {loss.item():.3f}")
    return model, sigma


@torch.no_grad()
def eval_agent(model, sigma, d: int, episodes: int, device, seed: int):
    """Behavioral evaluation at test demand d.  Returns (mean W_eff,
    p10, p90, self-consistency rate)."""
    rng = random.Random(seed)
    model.eval()
    ws, rates = [], []
    for _ in range(episodes):
        x, y, demand, closes = encode_episode(d, sigma, rng)
        xb = torch.from_numpy(x[None]).to(device)
        pred = model(xb)[0].argmax(-1).cpu().numpy()
        correct = {i: bool(pred[t] == y[t]) for (t, i) in closes}
        _, w_eff, rate = episode_metrics(demand, correct, d)
        ws.append(w_eff)
        rates.append(rate)
    ws = np.array(ws, float)
    return (float(ws.mean()), float(np.percentile(ws, 10)),
            float(np.percentile(ws, 90)), float(np.mean(rates)))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--smoke", action="store_true")
    ap.add_argument("--steps", type=int, default=None,
                    help="override training steps")
    ap.add_argument("--h", type=int, nargs="+", default=None,
                    help="override hidden sizes")
    ap.add_argument("--out", default=os.path.join(HERE, "money_plot_emergent"))
    args = ap.parse_args()
    log = print

    if args.smoke:
        h_list, steps, batch, ev_eps, seeds = [8], 300, 16, 5, 1
    elif args.quick:
        h_list, steps, batch, ev_eps, seeds = [4, 16, 64], 20_000, 64, 20, 1
    else:
        h_list, steps, batch, ev_eps, seeds = [4, 8, 16, 32, 64], 15_000, 64, 40, 2
    if args.steps is not None:
        steps = args.steps
    if args.h is not None:
        h_list = args.h

    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    log(f"[E'] device={device}, h={h_list}, steps={steps}, "
        f"seeds={seeds}, eval episodes={ev_eps}/point")

    demands = list(range(1, D_MAX + 1))
    results = {"h_list": h_list, "demands": demands, "q": Q,
               "steps": steps, "seeds": seeds, "curves": {}, "sat": {}}

    for h in h_list:
        per_seed_w = np.zeros((seeds, len(demands)))
        per_seed_lo = np.zeros_like(per_seed_w)
        per_seed_hi = np.zeros_like(per_seed_w)
        per_seed_rate = np.zeros_like(per_seed_w)
        for s in range(seeds):
            log(f"  training h={h} seed={s} ...")
            model, sigma = train_agent(h, steps, batch, device,
                                       seed=52_000 + 17 * h + s, log=log)
            for j, d in enumerate(demands):
                w, lo, hi, rate = eval_agent(model, sigma, d, ev_eps,
                                             device, seed=90_000 + 7 * d + s)
                per_seed_w[s, j] = w
                per_seed_lo[s, j] = lo
                per_seed_hi[s, j] = hi
                per_seed_rate[s, j] = rate
        results["curves"][str(h)] = {
            "mean": per_seed_w.mean(0).tolist(),
            "lo": per_seed_lo.mean(0).tolist(),
            "hi": per_seed_hi.mean(0).tolist(),
            "rate": per_seed_rate.mean(0).tolist(),
        }
        log(f"  h={h}  W_eff over d={demands}: "
            + ", ".join(f"{m:.2f}" for m in per_seed_w.mean(0)))

    # Saturation view: rate vs h at fixed demands (reuses curve data).
    for d_star in (3, 5, 7):
        j = demands.index(d_star)
        results["sat"][str(d_star)] = {
            "h": h_list,
            "rate": [results["curves"][str(h)]["rate"][j] for h in h_list],
        }

    with open(f"{args.out}_results.json", "w") as fh:
        json.dump(results, fh, indent=1)
    log(f"Wrote {args.out}_results.json")

    # ---------------- figure ----------------
    fig, (axE, axF) = plt.subplots(1, 2, figsize=(11.5, 4.8))
    cols = plt.cm.plasma(np.linspace(0.10, 0.75, len(h_list)))
    dd = np.array(demands, float)

    axE.plot(dd, dd, ":", color="0.35", lw=1.5, label="identity ($W=d$)")
    for h, col in zip(h_list, cols):
        cur = results["curves"][str(h)]
        axE.plot(demands, cur["mean"], "-o", color=col, label=f"$h = {h}$")
        axE.fill_between(demands, cur["lo"], cur["hi"], color=col, alpha=0.15)
    axE.set_xlabel("environment coordination demand $d$")
    axE.set_ylabel("achieved coordination width $W_{\\mathrm{eff}}$ (behavioral)")
    axE.set_title("E$'$.  Emergent matching law: GRU trained by SGD,\n"
                  "no designed frontier — capacity is a consequence\n"
                  "of parameters and training")
    axE.legend(frameon=False, fontsize=8)
    axE.grid(alpha=0.3)

    sat_cols = plt.cm.viridis(np.linspace(0.15, 0.8, 3))
    for (d_star, col) in zip((3, 5, 7), sat_cols):
        s = results["sat"][str(d_star)]
        axF.plot(s["h"], s["rate"], "-o", color=col,
                 label=f"test demand $d = {d_star}$")
    axF.set_xscale("log", base=2)
    axF.set_ylim(0, 1.05)
    axF.set_xlabel("hidden size $h$ (emergent capacity knob)")
    axF.set_ylabel("self-consistency rate")
    axF.set_title("F$'$.  Saturation, emergent version: capacity\n"
                  "beyond the environment's demand buys nothing")
    axF.legend(frameon=False, fontsize=8)
    axF.grid(alpha=0.3)

    fig.suptitle("Trained agents exhibit the same capacity ceiling as "
                 "designed agents (cf. panels C/D)", y=1.04, fontsize=13)
    fig.tight_layout()
    for ext in ("png", "pdf"):
        path = f"{args.out}.{ext}"
        fig.savefig(path, dpi=200, bbox_inches="tight")
        log(f"Wrote {path}")


if __name__ == "__main__":
    main()
