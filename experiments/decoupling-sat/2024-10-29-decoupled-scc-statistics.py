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

REVISION = "00353b511ad428e05851023144893db24cd38cff"
REVISIONS = [REVISION]

CONFIGS = []

searches = {"Esat-LP-F0.2s1M": ["--root-task-transform", "decoupled(factoring=lp(min_number_leaves=2, factoring_time_limit=30, strategy=mfa, add_cg_sccs=true, min_flexibility=0.2, max_leaf_size=1000000), global_leaf_effects=false)", "--search", "sat(encoding=2, plan_length=1)"],
}

DRIVER_OPTS = ["--overall-time-limit", "30m"]

for s_name, s_opt in searches.items():
    CONFIGS.append(IssueConfig(f'{s_name}', s_opt, driver_options=DRIVER_OPTS, build_options=["-s/home/x_dangn/bin/lib/", "--kissat"]))


ENVIRONMENT = TetralithEnvironment(
    email="daniel.gnad@liu.se",
#    time_limit_per_task="24:00:00",
#    memory_per_cpu="8300M",
    extra_options="#SBATCH -A naiss2024-5-404", # parground
#    extra_options="#SBATCH -A naiss2023-5-314", # dfsplan
)

exp = IssueExperiment(
    revisions=REVISIONS,
    configs=CONFIGS,
    environment=ENVIRONMENT,
)

exp.add_suite(BENCHMARKS_DIR, common_setup.DEFAULT_SATISFICING_SUITE)

exp.add_parser(exp.EXITCODE_PARSER)
exp.add_parser(exp.TRANSLATOR_PARSER)
exp.add_parser(exp.SINGLE_SEARCH_PARSER)
exp.add_parser(exp.PLANNER_PARSER)
exp.add_parser(sat_parser.SATParser())
exp.add_parser(decoupling_parser.DecouplingParser())

exp.add_step('build', exp.build)
exp.add_step('start', exp.start_runs)
exp.add_step("parse", exp.parse)

exp.add_fetcher(name='fetch')

common_setup.add_compress_and_delete_runs_step(exp)


FORMAT = "html"

# REPORT TABLES

def filter_kissat_oom(run):
    if "unexplained_errors" in run:
        if any("kissat: fatal error: out-of-memory" in x for x in run["unexplained_errors"]):
            del run["unexplained_errors"]
            run["error"] = "search-out-of-memory"
    return run

attributes = ['number_statically_true_dvars', 'percentage_statically_true_dvars']
for type in ["sizeone", "problematic-2ante", "implication", "onefact", "onefactinternal", "onevar", "onevarinternal", "problematic-general"]:
    attributes.append(f'number_{type}_sccs')
    attributes.append(f'min_size_{type}_sccs')
    attributes.append(f'max_size_{type}_sccs')
    attributes.append(f'sum_size_{type}_sccs')
    attributes.append(f'percentage_{type}_sccs')
    attributes.append(f'median_size_{type}_sccs')
    attributes.append(f'avg_size_{type}_sccs')


exp.add_report(AbsoluteReport(attributes=attributes, filter=[filter_kissat_oom]), outfile=f"{SCRIPT_NAME}.html")


exp.run_steps()


