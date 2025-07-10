#! /usr/bin/env python3

import os

from lab.environments import TetralithEnvironment
from lab.reports import Attribute, geometric_mean, arithmetic_mean

from downward.experiment import FastDownwardExperiment

from downward.reports.absolute import AbsoluteReport
from downward.reports.compare import ComparativeReport
from downward.reports.scatter import ScatterPlotReport

import common_setup

import filters

import sat_parser

DIR = os.path.dirname(os.path.abspath(__file__))
SCRIPT_NAME = os.path.splitext(os.path.basename(__file__))[0]

BENCHMARKS_DIR_AXIOMS = os.environ["BENCHMARKS_AXIOMS"]
BENCHMARKS_DIR_AXIOMS_CONDEFFS = os.environ["BENCHMARKS_AXIOMS_CONDEFFS"]

REPO = common_setup.get_repo_base()
REPO_SYMK = "/proj/parground/users/x_dangn/symk/"

REVISION = "a0441e9d47e9c34d4d2db1221ec0b8bd2bb93461"
REVISION_SYMK = "43b090cee3143d1fcd96a160d335066faf578a50"

common_options = ["--translate-options", "--skip-negative-axioms", "--search-options", "--root-task-transform", "sat_axiom()", "--search"]

searches = {"blind" : ["--translate-options", "--skip-negative-axioms", "--search-options", "--search", "astar(blind(transform=adapt_costs(cost_type=one)), cost_type=one)"],
            "sat": common_options + ["sat(encoding=0)"],
            "Esat": common_options + ["sat(encoding=2)"],
}

for k in range(18):
    searches[f"sat{k}"] = common_options + [f"sat(encoding=0, length_iteration={k})"]
    searches[f"Esat{k}"] = common_options + [f"sat(encoding=2, length_iteration={k})"]


DRIVER_OPTS =    ["--overall-time-limit", "30m", '--validate-time-limit', '5m', '--validate-memory-limit', '3584M']
DRIVER_OPTS_INC = ["--overall-time-limit", "7m", '--validate-time-limit', '5m', '--validate-memory-limit', '3584M']

BUILD_OPTS_SAT = ["-s/home/x_dangn/bin/lib/", "--kissat"] 


ENVIRONMENT = TetralithEnvironment(
    email="daniel.gnad@liu.se",
#    time_limit_per_task="24:00:00",
#    memory_per_cpu="8300M",
    extra_options="#SBATCH -A naiss2024-5-404", # parground
)

exp = FastDownwardExperiment(environment=ENVIRONMENT)

for s_name, s_opt in searches.items():
    if s_name in ["blind", "sat", "Esat"]:
        driver = DRIVER_OPTS 
    else:
        driver = DRIVER_OPTS_INC
    exp.add_algorithm(f'{s_name}', REPO, REVISION, s_opt, driver_options=driver, build_options=BUILD_OPTS_SAT)

exp.add_algorithm('lama-first', REPO, REVISION, [], driver_options=DRIVER_OPTS + ["--alias", "lama-first"], build_options=BUILD_OPTS_SAT)

exp.add_algorithm("SymK-bd", REPO_SYMK, REVISION_SYMK, ["--search", "sym_bd(cost_type=one)"], driver_options=DRIVER_OPTS)

exp.add_suite(BENCHMARKS_DIR_AXIOMS, common_setup.AXIOMS_SUITE)
exp.add_suite(BENCHMARKS_DIR_AXIOMS_CONDEFFS, common_setup.AXIOMS_CONDEFFS_SUITE)

exp.add_parser(exp.EXITCODE_PARSER)
exp.add_parser(exp.TRANSLATOR_PARSER)
exp.add_parser(exp.SINGLE_SEARCH_PARSER)
exp.add_parser(exp.PLANNER_PARSER)
exp.add_parser(sat_parser.SATParser())

exp.add_step('build', exp.build)
exp.add_step('start', exp.start_runs)
exp.add_step("parse", exp.parse)

exp.add_fetcher(name='fetch')

common_setup.add_compress_and_delete_runs_step(exp)


FORMAT = "html"

# REPORT TABLES
attributes = common_setup.ATTRIBUTES

def filter_kissat_oom(run):
    if "unexplained_errors" in run:
        if any("kissat: fatal error: out-of-memory" in x for x in run["unexplained_errors"]):
            del run["unexplained_errors"]
            run["error"] = "search-out-of-memory"
    return run



exp.add_report(AbsoluteReport(attributes=attributes, filter=[filters.remove_revision, filter_kissat_oom]), outfile=f"{SCRIPT_NAME}-raw.html")

TIME_LIMIT = 1800 # 30 min
MEMORY_LIMIT = 3584 * 1000 # 3584 MB

virtual_solver_filter = filters.VirtualSat(["sat17", "Esat17"], TIME_LIMIT, ["sat", "Esat"])

suffix = virtual_solver_filter.get_config_name_extension()


coverage_configs = ["blind", "SymK-bd", "sat", "Esat", f"sat-{suffix}", f"Esat-{suffix}", "lama-first"]
exp.add_report(AbsoluteReport(attributes=attributes, filter=[filters.remove_revision, filters.filter_kissat_oom, virtual_solver_filter.add_run, virtual_solver_filter.replace_config], filter_algorithm=coverage_configs),
               outfile=f"{SCRIPT_NAME}-{suffix}-all.html")

exp.add_report(AbsoluteReport(attributes=["coverage"], filter=[filters.remove_revision, filters.filter_kissat_oom, virtual_solver_filter.add_run, virtual_solver_filter.replace_config], filter_algorithm=coverage_configs, format="tex"),
               outfile=f"{SCRIPT_NAME}-{suffix}-coverage.tex")



# SCATTER PLOTS

PLOT_FORMAT = "png"

def add_actual_runtime(run):
    if run["coverage"] == 1:
        run["actual_runtime"] = run["translator_time_done"] + run["total_time"]
    return run

for c1, c2 in [("lama-first", f"Esat-{suffix}")]:
    for attr in ["actual_runtime", "plan_length"]:
        exp.add_report(
            ScatterPlotReport(
                attributes=[attr],
                filter=[filters.remove_revision, virtual_solver_filter.add_run, virtual_solver_filter.replace_config, add_actual_runtime],
                filter_algorithm=[c1, c2],
                get_category=lambda x,y: x["domain"] if PLOT_FORMAT == "tex" else None,
                format=PLOT_FORMAT,
                show_missing=attr == "actual_runtime",
            ),
            name=f"scatterplot-{attr}-{c1}-vs-{c2}",
        )


exp.run_steps()


