#! /usr/bin/env python3

import itertools
import math
import os
from pathlib import Path
import subprocess

from lab.environments import TetralithEnvironment
from lab.reports import Attribute, geometric_mean, arithmetic_mean

from downward.reports.absolute import AbsoluteReport
from downward.reports.compare import ComparativeReport
from downward.reports.scatter import ScatterPlotReport

import common_setup
from common_setup import IssueConfig, IssueExperiment

import filters

import decoupling_parser
import sat_parser

DIR = os.path.dirname(os.path.abspath(__file__))
SCRIPT_NAME = os.path.splitext(os.path.basename(__file__))[0]
BENCHMARKS_DIR = os.environ["DOWNWARD_BENCHMARKS"]
REVISION = "97c52a560f5805768570cdd227f1ae3938e5f9a0"
REVISIONS = [REVISION]

CONFIGS = []
factorings = {
    'LP-F0.2s1M':        'lp(min_number_leaves=2, factoring_time_limit=30, strategy=mfa, add_cg_sccs=true, min_flexibility=0.2, max_leaf_size=1000000)',
    'LP-L0.8s1M':        'lp(min_number_leaves=2, factoring_time_limit=30, strategy=mml, add_cg_sccs=true, min_flexibility=0.8, max_leaf_size=1000000)',
}
searches = {#"blind" : "astar(blind(), cost_type=one)",
            #"ff" : "lazy_greedy([ff(transform=adapt_costs(cost_type=one))], cost_type=one)",
            #"sat": "sat()",
}

for k in range(18):
    searches[f"sat{k}"] = f"sat(encoding=0, length_iteration={k})"
    searches[f"Esat{k}"] = f"sat(encoding=2, length_iteration={k})"

DRIVER_OPTS = ["--overall-time-limit", "5m"]

for s_name, s_opt in searches.items():
    #CONFIGS.append(IssueConfig(f'{s_name}', ['--search',  f'{s_opt}'], driver_options=DRIVER_OPTS, build_options=["-s/home/x_dangn/bin/lib/", "--kissat"]))
    for d_name, d_opt in factorings.items():
        CONFIGS.append(IssueConfig(f'{s_name}-{d_name}-clo', ['--root-task-transform', f"decoupled(factoring={d_opt}, global_leaf_effects=false)", '--search',  f'{s_opt}'], driver_options=DRIVER_OPTS, build_options=["-s/home/x_dangn/bin/lib/", "--kissat"]))


SUITE = common_setup.DEFAULT_SATISFICING_SUITE

ENVIRONMENT = TetralithEnvironment(
    email="daniel.gnad@liu.se",
#    time_limit_per_task="24:00:00",
#    memory_per_cpu="8300M",
    extra_options="#SBATCH -A naiss2024-5-404", # parground
#   extra_options="#SBATCH -A naiss2023-5-314", # dfsplan
)

exp = IssueExperiment(
    revisions=REVISIONS,
    configs=CONFIGS,
    environment=ENVIRONMENT,
)

exp.add_suite(BENCHMARKS_DIR, SUITE)

exp.add_parser(exp.EXITCODE_PARSER)
exp.add_parser(exp.TRANSLATOR_PARSER)
exp.add_parser(exp.SINGLE_SEARCH_PARSER)
exp.add_parser(exp.PLANNER_PARSER)
exp.add_parser(decoupling_parser.DecouplingParser())
exp.add_parser(sat_parser.SATParser())

exp.add_step('build', exp.build)
exp.add_step('start', exp.start_runs)
exp.add_step("parse", exp.parse)

exp.add_fetcher(name='fetch')


def filter_baseline_algorithms(run):
    alg = run["algorithm"]
    if alg in ["blind", "blind-LP-F0.2s1M", "ff", "ff-LP-F0.2s1M"]:
        return run
    return False

exp.add_fetcher("data/2024-09-03-fix-no-global-op-eval", name='fetch-baseline', filter=[filter_baseline_algorithms], merge=True)

SAT_REV = "97c52a560f5805768570cdd227f1ae3938e5f9a0"
exp.add_fetcher("data/2024-10-04-leaf-copy-ops-eval", name='fetch-sat', filter_algorithm=[f"{SAT_REV}-sat", f"{SAT_REV}-sat-LP-F0.2s1M", f"{SAT_REV}-Esat", f"{SAT_REV}-Esat-LP-F0.2s1M"], merge=True)

# incremental sat baslines
exp.add_fetcher("data/2024-10-10-non-dec-inc-eval", name='fetch-sat-non-decoupled', merge=True)

exp.add_fetcher("data/2024-10-11-encoding-3-eval", name='fetch-exists-aggressive', merge=True)


FORMAT = "html"

# REPORT TABLES
attributes = common_setup.ATTRIBUTES + ["length_iteration_solved"]

def filter_kissat_oom(run):
    if "unexplained_errors" in run:
        if any("kissat: fatal error: out-of-memory" in x for x in run["unexplained_errors"]):
            del run["unexplained_errors"]
            run["error"] = "search-out-of-memory"
    return run


virtual_solver_filter_mob = filters.VirtualSat(["sat17", "sat17-LP-F0.2s1M-clo", "sat17-LP-L0.8s1M-clo", "Esat17", "Esat17-LP-F0.2s1M-clo", "Esat17-LP-L0.8s1M-clo"], 1800, ["sat", "Esat"])

factoring_filter_mob = filters.NonDecoupledTaskFilter(["sat17-LP-F0.2s1M-clo", "Esat17-LP-F0.2s1M-clo"])

suffix = "inc"

algorithms = ["blind", "blind-LP-F0.2s1M", "blind-LP-L0.8s1M", 
              "sat", "sat-LP-F0.2s1M", "sat-LP-L0.8s1M", "sat-LP-F0.2s1M-clo", "sat-LP-L0.8s1M-clo", 
              "Esat", "Esat-LP-F0.2s1M", "Esat-LP-L0.8s1M", "Esat-LP-F0.2s1M-clo", "Esat-LP-L0.8s1M-clo", 
              "aEsat-LP-F0.2s1M-clo", "aEsat-LP-L0.8s1M-clo",
              f"sat-{suffix}", f"sat-{suffix}-LP-F0.2s1M-clo", f"sat-{suffix}-LP-L0.8s1M-clo",
              f"Esat-{suffix}", f"Esat-{suffix}-LP-F0.2s1M-clo", f"Esat-{suffix}-LP-L0.8s1M-clo",
              "ff", "ff-LP-F0.2s1M", "ff-LP-L0.8s1M"]

exp.add_report(AbsoluteReport(attributes=attributes, filter=[filters.remove_revision, factoring_filter_mob.add_runs, factoring_filter_mob.filter_non_decoupled_runs, filter_kissat_oom, virtual_solver_filter_mob.add_run, virtual_solver_filter_mob.replace_config], filter_algorithm=algorithms), outfile=f"{SCRIPT_NAME}-all-mobility.html")

virtual_solver_filter_leaf = filters.VirtualSat(["sat17", "sat17-LP-F0.2s1M-clo", "sat17-LP-L0.8s1M-clo", "Esat17", "Esat17-LP-F0.2s1M-clo", "Esat17-LP-L0.8s1M-clo"], 1800, ["sat", "Esat"])

factoring_filter_leaf = filters.NonDecoupledTaskFilter(["sat17-LP-L0.8s1M-clo", "Esat17-LP-L0.8s1M-clo"])

exp.add_report(AbsoluteReport(attributes=attributes, filter=[filters.remove_revision, factoring_filter_leaf.add_runs, factoring_filter_leaf.filter_non_decoupled_runs, filter_kissat_oom, virtual_solver_filter_leaf.add_run, virtual_solver_filter_leaf.replace_config], filter_algorithm=algorithms), outfile=f"{SCRIPT_NAME}-all-leaves.html")

# SCATTER PLOTS

PLOT_FORMAT = "png"

for c1, c2 in [("blind-LP-F0.2s1M", "sat-LP-F0.2s1M"), ("blind-LP-L1.0s1M", "sat-LP-L1.0s1M")]:
    exp.add_report(
        ScatterPlotReport(
            attributes=["planner_time"],
            filter_algorithm=[c1, c2],
            get_category=lambda x,y: x["domain"],
            format=PLOT_FORMAT,
            show_missing=True,
        ),
        name=f"scatterplot-planner-time-{c1}-vs-{c2}",
    )

exp.run_steps()

factoring_filter_mob.print_statistics()
factoring_filter_leaf.print_statistics()
