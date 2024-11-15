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
REVISION = "ba5f510db0511bcc0a7da87dd0c7892cf0516d59"
REVISIONS = [REVISION]

CONFIGS = []
factorings = {
#    'LP-F0.2s1M':        'lp(min_number_leaves=2, factoring_time_limit=30, strategy=mfa, add_cg_sccs=true, min_flexibility=0.2, max_leaf_size=1000000)',
    'LP-L0.8s1M':        'lp(min_number_leaves=2, factoring_time_limit=30, strategy=mml, add_cg_sccs=true, min_flexibility=0.8, max_leaf_size=1000000)',
}
searches = {#"blind" : "astar(blind(), cost_type=one)",
            #"ff" : "lazy_greedy([ff(transform=adapt_costs(cost_type=one))], cost_type=one)",
            #"sat": "sat()",
}

for k in range(18):
#    searches[f"sat{k}"] = f"sat(encoding=0, length_iteration={k})"
    searches[f"aEsat{k}"] = f"sat(encoding=3, length_iteration={k})"

DRIVER_OPTS = ["--overall-time-limit", "5m"]

KISSAT_PATH = "/proj/parground/users/x_dangn/kissat-p/build/"

for s_name, s_opt in searches.items():
    if s_name.startswith("sat"):
        CONFIGS.append(IssueConfig(f'{s_name}', ['--search',  f'{s_opt}'], driver_options=DRIVER_OPTS, build_options=[f"-s{KISSAT_PATH}", "--kissat"]))
    else:
        for d_name, d_opt in factorings.items():
            CONFIGS.append(IssueConfig(f'{s_name}-{d_name}-clo', ['--root-task-transform', f"decoupled(factoring={d_opt}, global_leaf_effects=false)", '--search',  f'{s_opt}'], driver_options=DRIVER_OPTS, build_options=[f"-s{KISSAT_PATH}", "--kissat"]))


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

common_setup.add_compress_and_delete_runs_step(exp)


def rename_configs(run):
    if "LP-L0" not in run["algorithm"]:
        # configs which maximize number of leaves
        return False
    run["algorithm"] = f"{run['algorithm']}-old"
    return run


exp.add_fetcher("data/2024-10-14-aggressive-exists-inc-eval", name='fetch-aggressive-exists-inc', filter=[rename_configs], merge=True)


FORMAT = "html"

# REPORT TABLES
attributes = common_setup.ATTRIBUTES


virtual_solver_filter_leaf = filters.VirtualSat(["aEsat17-LP-L0.8s1M-clo", "aEsat17-LP-L0.8s1M-clo-old"], 1800, ["aEsat"])
virtual_solver_filter_leaf = filters.VirtualSatRoundRobin(["aEsat17-LP-L0.8s1M-clo", "aEsat17-LP-L0.8s1M-clo-old"], 1800, 3500, ["aEsat"])

factoring_filter_leaf = filters.NonDecoupledTaskFilter()

suffix = virtual_solver_filter_leaf.get_config_name_extension()

exp.add_report(AbsoluteReport(attributes=attributes, filter=[filters.remove_revision, factoring_filter_leaf.add_runs, factoring_filter_leaf.filter_non_decoupled_runs, filters.filter_kissat_oom, virtual_solver_filter_leaf.add_run, virtual_solver_filter_leaf.replace_config]), outfile=f"{SCRIPT_NAME}-{suffix}-all.html")

exp.add_report(AbsoluteReport(attributes=attributes, filter=[filters.remove_revision, factoring_filter_leaf.add_runs, factoring_filter_leaf.filter_non_decoupled_runs, filters.filter_kissat_oom, virtual_solver_filter_leaf.add_run, virtual_solver_filter_leaf.replace_config], filter_algorithm=[f"aEsat-{suffix}-LP-L0.8s1M-clo", f"aEsat-{suffix}-LP-L0.8s1M-clo-old"]), outfile=f"{SCRIPT_NAME}-{suffix}-combined.html")

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

virtual_solver_filter_leaf.print_statistics()
factoring_filter_leaf.print_statistics()
