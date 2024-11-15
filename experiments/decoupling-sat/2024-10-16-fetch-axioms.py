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


exp = Experiment()


exp.add_fetcher("data/2024-10-15-axiom-domains-baselines-eval", name='fetch-baselines')

#SAT_REV = "3b36f26e9106d2689776450a9dfa2af01fe4ef7d"
#exp.add_fetcher("data/2024-10-15-axiom-domains-sat-eval", name='fetch-sat', filter_algorithm=[f"{SAT_REV}-sat"], merge=True) # outdated

#exp.add_fetcher("data/2024-10-16-axiom-domains-esat-eval", name='fetch-esat', merge=True) # outdated

#exp.add_fetcher("data/2024-10-16-axiom-domains-sat-inc-eval", name='fetch-sat-inc', merge=True) # outdated

exp.add_fetcher("data/2024-10-17-axiom-domains-sat-eval", name='fetch-sat', merge=True)

exp.add_fetcher("data/2024-10-18-axiom-domains-sat-inc-eval", name='fetch-sat-inc', merge=True)

#exp.add_fetcher("data/2024-10-23-axiom-domains-sat-inc-modified-kissat-eval", name='fetch-sat-inc-mod-kissat', merge=True)

exp.add_fetcher("/proj/parground/users/x_dangn/symk/experiments/symk-axioms/data/2024-10-18-symbd-axiom-domains-eval", name='fetch-symK', merge=True)

FORMAT = "html"

# REPORT TABLES
attributes = common_setup.ATTRIBUTES

TIME_LIMIT = 1800 # 30 min
MEMORY_LIMIT = 3584 * 1000 # 3584 MB

virtual_solver_filter = filters.VirtualSat(["sat17", "Esat17"], TIME_LIMIT, ["sat", "Esat"])
#virtual_solver_filter = filters.VirtualSatRoundRobin(["sat17", "Esat17"], TIME_LIMIT, MEMORY_LIMIT, ["sat", "Esat"])


suffix = virtual_solver_filter.get_config_name_extension()

algorithms = ["blind", "sat", "Esat", f"sat-{suffix}", f"Esat-{suffix}", "ff", "ff-pref", "lama-first", "symBD"]

exp.add_report(AbsoluteReport(attributes=attributes, filter=[filters.remove_revision, filters.filter_kissat_oom, virtual_solver_filter.add_run, virtual_solver_filter.replace_config], filter_algorithm=algorithms),
               outfile=f"{SCRIPT_NAME}-{suffix}-all.html")

coverage_configs = ["blind", "symBD", "sat", "Esat", f"sat-{suffix}", f"Esat-{suffix}", "lama-first"]
exp.add_report(AbsoluteReport(attributes=["coverage"], filter=[filters.remove_revision, filters.filter_kissat_oom, virtual_solver_filter.add_run, virtual_solver_filter.replace_config], filter_algorithm=coverage_configs, format="tex"),
               outfile=f"{SCRIPT_NAME}-{suffix}-coverage.tex")

# SCATTER PLOTS

PLOT_FORMAT = "tex"

def add_actual_runtime(run):
    if run["coverage"] == 1:
        run["actual_runtime"] = run["translator_time_done"] + run["total_time"]
    return run

for c1, c2 in [("lama-first", f"Esat-{suffix}")]:
    exp.add_report(
        ScatterPlotReport(
            attributes=["actual_runtime"],
            filter=[filters.remove_revision, virtual_solver_filter.add_run, virtual_solver_filter.replace_config, add_actual_runtime],
            filter_algorithm=[c1, c2],
            #get_category=lambda x,y: x["domain"],
            format=PLOT_FORMAT,
            show_missing=True,
        ),
        name=f"scatterplot-planner-time-{c1}-vs-{c2}",
    )

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

virtual_solver_filter.print_statistics()
