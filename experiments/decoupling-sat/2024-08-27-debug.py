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

DIR = os.path.dirname(os.path.abspath(__file__))
SCRIPT_NAME = os.path.splitext(os.path.basename(__file__))[0]
BENCHMARKS_DIR = os.environ["DOWNWARD_BENCHMARKS"]
REVISION = "c539b2477432ddaf085072869edd629eb900d5db"
REVISIONS = [REVISION]

CONFIGS = []
factorings = {
    'LP-F0.2s1M':        'lp(min_number_leaves=2, factoring_time_limit=30, strategy=mfa, add_cg_sccs=true, min_flexibility=0.2, max_leaf_size=1000000)',
    'LP-L1.0s1M':        'lp(min_number_leaves=2, factoring_time_limit=30, strategy=mml, add_cg_sccs=true, min_flexibility=1.0, max_leaf_size=1000000)',
}
searches = {"blind" : "astar(blind(), cost_type=one)",
            "ff" : "lazy_greedy([ff(transform=adapt_costs(cost_type=one))], cost_type=one)",
            "sat": "sat()",
}

DRIVER_OPTS = ["--overall-time-limit", "5m"]

for s_name, s_opt in searches.items():
    CONFIGS.append(IssueConfig(f'{s_name}', ['--search',  f'{s_opt}'], driver_options=DRIVER_OPTS, build_options=["-s/home/x_dangn/bin/lib/", "--kissat"]))
    for d_name, d_opt in factorings.items():
        CONFIGS.append(IssueConfig(f'{s_name}-{d_name}', ['--root-task-transform', f"decoupled(factoring={d_opt})", '--search',  f'{s_opt}'], driver_options=DRIVER_OPTS, build_options=["-s/home/x_dangn/bin/lib/", "--kissat"]))


SUITE = common_setup.DEFAULT_SATISFICING_SUITE

ENVIRONMENT = TetralithEnvironment(
    email="daniel.gnad@liu.se",
#    time_limit_per_task="24:00:00",
#    memory_per_cpu="8300M",
#    extra_options="#SBATCH -A naiss2023-5-236", # parground
    extra_options="#SBATCH -A naiss2023-5-314", # dfsplan
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

exp.add_step('build', exp.build)
exp.add_step('start', exp.start_runs)
exp.add_step("parse", exp.parse)

exp.add_fetcher(name='fetch', filter=[filters.remove_revision])


FORMAT = "html"

# REPORT TABLES
attributes = common_setup.ATTRIBUTES

def filter_kissat_oom(run):
    if "unexplained_errors" in run:
        if any("kissat: fatal error: out-of-memory" in x for x in run["unexplained_errors"]):
            del run["unexplained_errors"]
            run["error"] = "search-out-of-memory"
    return run

def remove_ff_configs(run):
    if "ff" in run["algorithm"]:
        return False
    return run

exp.add_report(AbsoluteReport(attributes=attributes, filter=[filter_kissat_oom]), outfile=f"{SCRIPT_NAME}-all.html")


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


