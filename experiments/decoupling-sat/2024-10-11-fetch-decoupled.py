#! /usr/bin/env python3

import itertools
import math
import os
from pathlib import Path
import subprocess

from lab.reports import Attribute, geometric_mean, arithmetic_mean
from lab.experiment import Experiment

from downward.reports.absolute import AbsoluteReport
from downward.reports.compare import ComparativeReport
from downward.reports.scatter import ScatterPlotReport

import common_setup

import filters

DIR = os.path.dirname(os.path.abspath(__file__))
SCRIPT_NAME = os.path.splitext(os.path.basename(__file__))[0]

factorings = ['LP-F0.2s1M', 'LP-L0.8s1M']


exp = Experiment()


exp.add_fetcher("data/2024-10-11-decoupled-baselines-eval", name='fetch-dec-baselines', merge=True)

exp.add_fetcher("data/2024-10-11-encoding-3-eval", name='fetch-aggressive-exists', merge=True)

exp.add_fetcher("data/2024-10-10-non-dec-inc-eval", name='fetch-non-decoupled-incremental', merge=True)

SAT_REV = "97c52a560f5805768570cdd227f1ae3938e5f9a0"
exp.add_fetcher("data/2024-10-04-leaf-copy-ops-eval", name='fetch-sat-non-inc', filter_algorithm=[f"{SAT_REV}-sat", f"{SAT_REV}-sat-LP-F0.2s1M-clo", f"{SAT_REV}-Esat", f"{SAT_REV}-Esat-LP-F0.2s1M-clo"], merge=True)

algs = [f"{SAT_REV}-{sat}{count}-{factoring}-clo" for count in range(18) for factoring in factorings for sat in ["sat", "Esat"]]
algs += [f"{SAT_REV}-{sat}{count}-{factoring}" for count in range(18) for factoring in factorings for sat in ["sat", "Esat"]]
exp.add_fetcher("data/2024-10-07-copy-ops-inc-eval", name='fetch-sat-inc', filter_algorithm=algs, merge=True)

exp.add_fetcher("data/2024-10-12-copy-ops-leaf-eval", name='fetch-decoupled-leaf', merge=True)

exp.add_fetcher("data/2024-10-12-plain-ops-eval", name='fetch-decoupled-plain-ops', merge=True)

exp.add_fetcher("data/2024-11-01-plain-ops-inc-eval", name='fetch-decoupled-plain-ops-inc', merge=True)

exp.add_fetcher("data/2024-10-12-encoding-3-plain-ops-eval", name='fetch-aggressive-esat-plain-ops', merge=True)

# NOTE: results were not too convincing, almost no difference in runtime, number disabling graph SCCs increased nicely in some domains, though
#exp.add_fetcher("data/2024-10-14-copy-ops-leaf-batched-eval", name='fetch-esat-batched-copy-ops', merge=True)

exp.add_fetcher("data/2024-10-14-aggressive-exists-inc-eval", name='fetch-aggressive-exists-inc', merge=True)

exp.add_fetcher("data/2024-10-15-madagascar-eval", name='fetch-madagascar', merge=True)

FORMAT = "html"

# REPORT TABLES
attributes = common_setup.ATTRIBUTES


#virtual_solver_filter_mob = filters.VirtualSat(["sat17", "sat17-LP-F0.2s1M-clo", "sat17-LP-L0.8s1M-clo", "Esat17", "Esat17-LP-F0.2s1M-clo", "Esat17-LP-L0.8s1M-clo", "aEsat17-LP-F0.2s1M-clo", "aEsat17-LP-L0.8s1M-clo"], 1800, ["sat", "Esat", "aEsat"])

factoring_filter_mob = filters.NonDecoupledTaskFilter(["sat1-LP-F0.2s1M-clo", "Esat-LP-F0.2s1M-clo", "blind-LP-F0.2s1M"])

suffix = "inc"

# TODO possibly add aggressive exists step with copy op batching both regular and incremental
#algorithms = ["blind", "blind-LP-F0.2s1M", "blind-LP-L0.8s1M", 
#              "sat", "sat-LP-F0.2s1M", "sat-LP-L0.8s1M", "sat-LP-F0.2s1M-clo", "sat-LP-L0.8s1M-clo", 
#              "Esat", "Esat-LP-F0.2s1M", "Esat-LP-L0.8s1M", "Esat-LP-F0.2s1M-clo", "Esat-LP-L0.8s1M-clo", #"Esat-LP-F0.2s1M-cloB", "Esat-LP-L0.8s1M-cloB",
#              "aEsat-LP-F0.2s1M-clo", "aEsat-LP-L0.8s1M-clo",
#              f"sat-{suffix}", f"sat-{suffix}-LP-F0.2s1M-clo", f"sat-{suffix}-LP-L0.8s1M-clo",
#              f"Esat-{suffix}", f"Esat-{suffix}-LP-F0.2s1M-clo", f"Esat-{suffix}-LP-L0.8s1M-clo", f"aEsat-{suffix}-LP-F0.2s1M-clo", f"aEsat-{suffix}-LP-L0.8s1M-clo",
#              "ff", "ff-LP-F0.2s1M", "ff-LP-L0.8s1M",
#              "ff-pref", "ff-pref-LP-F0.2s1M", "ff-pref-LP-L0.8s1M",
#              "lama-first", "dec-lama-first-F0.2s1M", "dec-lama-first-L0.8s1M"]
#
#exp.add_report(AbsoluteReport(attributes=attributes, filter=[filters.remove_revision, factoring_filter_mob.add_runs, factoring_filter_mob.filter_non_decoupled_runs, filters.filter_kissat_oom, virtual_solver_filter_mob.add_run, virtual_solver_filter_mob.replace_config], filter_algorithm=algorithms), outfile=f"{SCRIPT_NAME}-all-mobility.html")

#virtual_solver_filter_leaf = filters.VirtualSat(["sat17", "sat17-LP-L0.8s1M", "sat17-LP-L0.8s1M-clo", "Esat17", "Esat17-LP-L0.8s1M", "Esat17-LP-L0.8s1M-clo", "aEsat17-LP-L0.8s1M-clo"], 1800, ["sat", "Esat", "aEsat"])

factoring_filter_leaf = filters.NonDecoupledTaskFilter(["sat1-LP-L0.8s1M-clo", "Esat-LP-L0.8s1M-clo", "blind-LP-L0.8s1M"])

#exp.add_report(AbsoluteReport(attributes=attributes, filter=[filters.remove_revision, factoring_filter_leaf.add_runs, factoring_filter_leaf.filter_non_decoupled_runs, filters.filter_kissat_oom, virtual_solver_filter_leaf.add_run, virtual_solver_filter_leaf.replace_config], filter_algorithm=algorithms), outfile=f"{SCRIPT_NAME}-all-leaves.html")


# report with madagascar
algorithms = ["blind",# "blind-LP-L0.8s1M", 
              "sat", "sat-LP-L0.8s1M", "sat-LP-L0.8s1M-clo", 
              "Esat", "Esat-LP-L0.8s1M", "Esat-LP-L0.8s1M-clo", "aEsat-LP-L0.8s1M-clo",
              f"sat-{suffix}", f"sat-{suffix}-LP-L0.8s1M", f"sat-{suffix}-LP-L0.8s1M-clo",
              f"Esat-{suffix}", f"Esat-{suffix}-LP-L0.8s1M", f"Esat-{suffix}-LP-L0.8s1M-clo", f"aEsat-{suffix}-LP-L0.8s1M-clo",
              #"MpC-seq", 
              "MpC-RR-P0", "MpC-RR-P2", 
              #"ff-pref", "ff-pref-LP-F0.2s1M", "ff-pref-LP-L0.8s1M",
              "lama-first", "dec-lama-first-L0.8s1M"]

#virtual_solver_filter_leaf_M = filters.VirtualSat(["sat17", "sat17-LP-F0.2s1M-clo", "Esat17", "aEsat17-LP-F0.2s1M-clo"], 1800, ["sat", "Esat", "aEsat"])
virtual_solver_filter_leaf_L = filters.VirtualSat(["sat17", "sat17-LP-L0.8s1M", "sat17-LP-L0.8s1M-clo", "Esat17", "Esat17-LP-L0.8s1M", "Esat17-LP-L0.8s1M-clo", "aEsat17-LP-L0.8s1M-clo"], 1800, ["sat", "Esat", "aEsat"])

exp.add_report(AbsoluteReport(attributes=attributes, filter=[filters.remove_revision, filters.filter_madagascar_known_unexplained_errors, filters.filter_kissat_oom, factoring_filter_leaf.add_runs, factoring_filter_leaf.filter_non_decoupled_runs, virtual_solver_filter_leaf_L.add_run, virtual_solver_filter_leaf_L.replace_config], filter_algorithm=algorithms), outfile=f"{SCRIPT_NAME}-madagascar.html")

exp.add_report(AbsoluteReport(attributes=["coverage"], filter=[filters.remove_revision, filters.filter_madagascar_known_unexplained_errors, filters.filter_kissat_oom, factoring_filter_leaf.add_runs, factoring_filter_leaf.filter_non_decoupled_runs, virtual_solver_filter_leaf_L.add_run, virtual_solver_filter_leaf_L.replace_config], filter_algorithm=algorithms, format="tex"), outfile=f"{SCRIPT_NAME}-coverage.tex")

# SCATTER PLOTS

PLOT_FORMAT = "png"

#for c1, c2 in [("blind-LP-F0.2s1M", "sat-LP-F0.2s1M"), ("blind-LP-L1.0s1M", "sat-LP-L1.0s1M")]:
#    exp.add_report(
#        ScatterPlotReport(
#            attributes=["planner_time"],
#            filter_algorithm=[c1, c2],
#            get_category=lambda x,y: x["domain"],
#            format=PLOT_FORMAT,
#            show_missing=True,
#        ),
#        name=f"scatterplot-planner-time-{c1}-vs-{c2}",
#    )

#attributes = ["planner_time", "number_disabling_graph_sccs", "task_size"]
#for c1, c2 in [("Esat-LP-F0.2s1M-clo", "Esat-LP-F0.2s1M-cloB"), ("Esat-LP-L0.8s1M-clo", "Esat-LP-L0.8s1M-cloB")]:
#    for attr in attributes:
#        exp.add_report(
#            ScatterPlotReport(
#                attributes=[attr],
#                filter=[filters.remove_revision],
#                filter_algorithm=[c1, c2],
#                get_category=lambda x,y: x["domain"],
#                format=PLOT_FORMAT,
#                show_missing=True,
#            ),
#            name=f"scatterplot-{attr}-{c1}-vs-{c2}",
#        )

exp.run_steps()

factoring_filter_mob.print_statistics()
factoring_filter_leaf.print_statistics()
