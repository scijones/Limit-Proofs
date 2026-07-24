"""Regenerate the money-plot figures from money_plot_results.json
without rerunning the experiments."""
import json, os, importlib.util

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location(
    "mp", os.path.join(HERE, "treewidth_money_plot.py"))
mp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mp)

data = json.load(open(os.path.join(HERE, "money_plot_results.json")))
mp.make_figures(data.get("csp"), data.get("cap"), data.get("rl"),
                os.path.join(HERE, "money_plot"), print)
