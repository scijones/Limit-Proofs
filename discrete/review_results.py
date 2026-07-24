import json, os
HERE = os.path.dirname(os.path.abspath(__file__))
d = json.load(open(os.path.join(HERE, "money_plot_results.json")))
csp, cap = d.get("csp"), d.get("cap")

if csp:
    print("=== CSP (panels A/B) ===")
    print("widths", csp["widths"], "Ts", csp["Ts"], "node cap", csp["node_cap"])
    if "p_grid" in csp:
        print("p grid", csp["p_grid"])
    for T in csp["Ts"]:
        n = csp["m"] * T
        for w in csp["widths"]:
            r = csp["runs"][f"T{T}_w{w}"]
            extra = f" at p={r.get('peak_p')}" if "peak_p" in r else ""
            print(f"  n={n:4d} w={w}: peak median={r['median']:>10.0f}{extra}"
                  f"  censored={r['censored_frac']:.0%}  sat={r.get('sat_frac', float('nan')):.0%}")
        # per-p detail for largest w
        w = csp["widths"][-1]
        r = csp["runs"][f"T{T}_w{w}"]
        if "by_p" in r:
            print(f"    [detail w={w}] " + "  ".join(
                f"p={p}:{v['median']:.0f}({v['censored_frac']:.0%}c,{v['sat_frac']:.0%}s)"
                for p, v in r["by_p"].items()))
    print()

if cap:
    print("=== CAP (panel C: matching law) ===")
    print("demands", cap["demands"], " instances", cap["instances"])
    for kk in [str(k) for k in cap["kappas"]]:
        cur = cap["curves"][kk]
        print(f"  kappa={kk:>4s}  mean: " + " ".join(f"{m:5.2f}" for m in cur["mean"]))
        print(f"             p10 : " + " ".join(f"{m:5.1f}" for m in cur["lo"]))
        print(f"             p90 : " + " ".join(f"{m:5.1f}" for m in cur["hi"]))
    print()
    print("=== SAT (panel D: saturation) ===")
    for dd in sorted(cap["sat"], key=int):
        s = cap["sat"][dd]
        print(f"  d={dd}  kappas {s['kappas']}")
        print(f"        mean: " + " ".join(f"{m:5.2f}" for m in s["mean"]))
