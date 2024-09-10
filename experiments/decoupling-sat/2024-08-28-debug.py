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
REVISION = "e1ba72cb08b88301e42f2384d7164244f5299225"
REVISIONS = [REVISION]

CONFIGS = []
factorings = {
    'LP-F0.2s1M':        'lp(min_number_leaves=2, factoring_time_limit=30, strategy=mfa, add_cg_sccs=true, min_flexibility=0.2, max_leaf_size=1000000)',
    'LP-L1.0s1M':        'lp(min_number_leaves=2, factoring_time_limit=30, strategy=mml, add_cg_sccs=true, min_flexibility=1.0, max_leaf_size=1000000)',
}
searches = {#"blind" : "astar(blind(), cost_type=one)",
            #"ff" : "lazy_greedy([ff(transform=adapt_costs(cost_type=one))], cost_type=one)",
            "sat": "sat()",
}

for k in range(5,26,5):
    searches[f"sat{k}"] = f"sat(length_iteration={k})"

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

exp.add_fetcher("data/2024-08-27-debug-eval/", name='fetch-base', filter_algorithm=["blind", "blind-LP-F0.2s1M", "blind-LP-L1.0s1M", "ff", "ff-LP-F0.2s1M", "ff-LP-L1.0s1M"], merge=True)

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

class VirtualSat:
    def __init__(self, replace_configs, time_limit):
        from collections import defaultdict
        self.replace_configs = replace_configs
        self.time_limit = time_limit
        self.cumulative_time_per_inst = defaultdict(lambda: defaultdict(list))
        self.planner_memory_per_inst = defaultdict(lambda: defaultdict(int))

    def get_run_length_and_factoring(run):
        alg = run["algorithm"]
        parts = alg.split("-", 1)
        length = int(parts[0][3:])
        if len(parts) == 1:
            # config is something like satXX
            return length, ""
        else:
            # config is something like satXX-factoring
            return length, parts[1]

    def add_run(self, run):
        alg = run["algorithm"]
        if alg.startswith("sat") and alg != "sat" and not alg.startswith("sat-"):
            length, factoring = VirtualSat.get_run_length_and_factoring(run)
            inst = f"{run['domain']}:{run['problem']}"
            if run["coverage"] == 1:
                if all(solved == 0 or l > length for solved, l, _ in self.cumulative_time_per_inst[factoring][inst]):
                    self.planner_memory_per_inst[factoring][inst] = run["planner_memory"]
                self.cumulative_time_per_inst[factoring][inst].append((length, 1, run["planner_time"]))
            else:
                self.cumulative_time_per_inst[factoring][inst].append((length, 0, run["planner_wall_clock_time"]))
        return run

    def replace_config(self, run):
        if run["algorithm"] in self.replace_configs:
            name_parts = run['algorithm'].split('-', 1)
            factoring = name_parts[1] if len(name_parts) > 1 else ''
            run["algorithm"] = f"{name_parts[0][:3]}-inc-{factoring}"
            for attr in ["coverage", "planner_time", "planner_memory", "cost", "search_time", "total_time", "memory"]:
                # better don't show this info instead of showing wrong info
                if attr in run:
                    del run[attr]
            inst = f"{run['domain']}:{run['problem']}"
            results = sorted(self.cumulative_time_per_inst[factoring][inst])
            sum_time = 0.0
            coverage = 0
            for length, solved, time in results:
                sum_time += time
                if solved == 1:
                    if sum_time <= self.time_limit:
                        coverage = 1
                    break
            if coverage == 1:
                run["error"] = "success"
                run["coverage"] = 1
                run["planner_time"] = sum_time
                run["planner_memory"] = self.planner_memory_per_inst[factoring][inst]
            else:
                run["error"] = "search-out-of-time"
                run["coverage"] = 0
        return run


virtual_solver_filter = VirtualSat(["sat25-LP-F0.2s1M", "sat25-LP-L1.0s1M", "sat25"], 300)

exp.add_report(AbsoluteReport(attributes=attributes, filter=[filter_kissat_oom, virtual_solver_filter.add_run, virtual_solver_filter.replace_config],
                              filter_algorithm=["blind", "blind-LP-F0.2s1M", "blind-LP-L1.0s1M", 
                                                "sat", "sat-LP-F0.2s1M", "sat-LP-L1.0s1M", 
                                                "sat-inc-", "sat-inc-LP-F0.2s1M", "sat-inc-LP-L1.0s1M",
                                                "ff", "ff-LP-F0.2s1M", "ff-LP-L1.0s1M"]), outfile=f"{SCRIPT_NAME}-all.html")


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


