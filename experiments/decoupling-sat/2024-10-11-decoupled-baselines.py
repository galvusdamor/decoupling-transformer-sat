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
REVISION = "c6651d718a00bc2edc515792dd496b8aa5cb7795"
REVISIONS = [REVISION]

CONFIGS = []
factorings = {
    'LP-F0.2s1M':        'lp(min_number_leaves=2, factoring_time_limit=30, strategy=mfa, add_cg_sccs=true, min_flexibility=0.2, max_leaf_size=1000000)',
    'LP-L0.8s1M':        'lp(min_number_leaves=2, factoring_time_limit=30, strategy=mml, add_cg_sccs=true, min_flexibility=0.8, max_leaf_size=1000000)',
}
searches = {"blind" : [[], "astar(blind(), cost_type=one)"],
            "ff" : [[], "lazy_greedy([ff(transform=adapt_costs(cost_type=one))], cost_type=one)"],
            "ff-pref" : [["--heuristic", "hff=ff(transform=adapt_costs(cost_type=one))"], "lazy_greedy([hff], preferred=[hff], cost_type=one)"], 
}

DRIVER_OPTS = ["--overall-time-limit", "30m"]

for s_name, conf in searches.items():
    h_pred, s_opt = conf
    CONFIGS.append(IssueConfig(f'{s_name}', h_pred + ['--search',  f'{s_opt}'], driver_options=DRIVER_OPTS, build_options=["-s/home/x_dangn/bin/lib/", "--kissat"]))
    for d_name, d_opt in factorings.items():
        CONFIGS.append(IssueConfig(f'{s_name}-{d_name}', h_pred + ['--root-task-transform', f"decoupled(factoring={d_opt})", '--search',  f'{s_opt}'], driver_options=DRIVER_OPTS, build_options=["-s/home/x_dangn/bin/lib/", "--kissat"]))

CONFIGS.append(IssueConfig('lama-first', [], driver_options=DRIVER_OPTS + ["--alias", "lama-first"], build_options=["-s/home/x_dangn/bin/lib/", "--kissat"]))
CONFIGS.append(IssueConfig('dec-lama-first-F0.2s1M', [], driver_options=DRIVER_OPTS + ["--alias", "decoupled-lama-first"], build_options=["-s/home/x_dangn/bin/lib/", "--kissat"]))
CONFIGS.append(IssueConfig('dec-lama-first-L0.8s1M', [], driver_options=DRIVER_OPTS + ["--alias", "decoupled-lama-first-leaves08"], build_options=["-s/home/x_dangn/bin/lib/", "--kissat"]))

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

exp.add_step('build', exp.build)
exp.add_step('start', exp.start_runs)
exp.add_step("parse", exp.parse)

exp.add_fetcher(name='fetch')

common_setup.add_compress_and_delete_runs_step(exp)

FORMAT = "html"

# REPORT TABLES
attributes = common_setup.ATTRIBUTES + ["length_iteration_solved"]

def filter_kissat_oom(run):
    if "unexplained_errors" in run:
        if any("kissat: fatal error: out-of-memory" in x for x in run["unexplained_errors"]):
            del run["unexplained_errors"]
            run["error"] = "search-out-of-memory"
    return run

exp.add_report(AbsoluteReport(attributes=attributes, filter=[filter_kissat_oom],), outfile=f"{SCRIPT_NAME}-all.html")

exp.run_steps()
