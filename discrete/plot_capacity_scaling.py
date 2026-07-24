"""Capacity-vs-substrate scaling plot (Panel G) from existing
money_plot_emergent_results.json.  No retraining.

Claim made visual: each DOUBLING of hidden state buys ~one unit of
achieved coordination width -- emergent capacity is logarithmic in
substrate, the supply-side face of the exponential exchange rate.
"""
import json
import os

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
res = json.load(open(os.path.join(HERE, "money_plot_emergent_results.json")))

h_list = res["h_list"]
demands = res["demands"]

# Plateau capacity: mean W_eff over the top demand bins (d >= 6),
# where every h is demand-saturated (capacity < demand for all but
# the largest h, for which it is a lower bound).
top = [j for j, d in enumerate(demands) if d >= 6]
cap = []
for h in h_list:
    m = res["curves"][str(h)]["mean"]
    cap.append(float(np.mean([m[j] for j in top])))

fig, ax = plt.subplots(figsize=(6.2, 4.8))
hs = np.array(h_list, float)

# log2 reference through the data (least squares on log2 h)
A = np.vstack([np.log2(hs), np.ones_like(hs)]).T
slope, icept = np.linalg.lstsq(A, np.array(cap), rcond=None)[0]
href = np.array([hs[0] * 0.8, hs[-1] * 1.25])
ax.plot(href, slope * np.log2(href) + icept, "--", color="0.4", lw=1.5,
        label=f"$W = {slope:.2f}\\,\\log_2 h {icept:+.2f}$ (fit)")

ax.plot(hs, cap, "o-", color="#C62828", ms=9, lw=2,
        label="measured emergent capacity")
for h, c in zip(h_list, cap):
    ax.annotate(f"{c:.1f}", (h, c), textcoords="offset points",
                xytext=(0, 9), ha="center", fontsize=9)

ax.set_xscale("log", base=2)
ax.set_xticks(h_list)
ax.set_xticklabels([str(h) for h in h_list])
ax.set_xlabel("hidden state size $h$ (log scale)")
ax.set_ylabel("achieved coordination width (plateau $W_{\\mathrm{eff}}$)")
ax.set_title("G.  Each doubling of substrate buys $\\approx$ one unit of\n"
             "coordination width: emergent capacity is logarithmic in\n"
             "resources (GRU + SGD; supply-side of the exchange rate)")
ax.grid(alpha=0.3, which="both")
ax.legend(frameon=False, fontsize=9, loc="upper left")
fig.tight_layout()

for ext in ("png", "pdf"):
    p = os.path.join(HERE, f"money_plot_scaling.{ext}")
    fig.savefig(p, dpi=200, bbox_inches="tight")
    print("Wrote", p)
print("capacities:", dict(zip(h_list, [round(c, 2) for c in cap])),
      f"| fitted slope {slope:.2f} per doubling")
