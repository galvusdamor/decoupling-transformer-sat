#! /usr/bin/env python3

import itertools
import math
import os
from pathlib import Path
import subprocess

from lab.environments import TetralithEnvironment
from lab.reports import Attribute, geometric_mean, arithmetic_mean
from lab.experiment import Experiment

from downward import suites
from downward.reports.absolute import AbsoluteReport
from downward.reports.compare import ComparativeReport
from downward.reports.scatter import ScatterPlotReport

import common_setup
import filters
import madagascar_parser

DIR = os.path.dirname(os.path.abspath(__file__))
SCRIPT_NAME = os.path.splitext(os.path.basename(__file__))[0]
BENCHMARKS_DIR = os.environ["DOWNWARD_BENCHMARKS"]

CONFIGS = [
    ("MpC-seq", ["-P", "0", "-S", "1", "-A", "1"]),
    ("MpC-RR-P0", ["-P", "0"]),
    ("MpC-RR-P2", ["-P", "2"]),
]

TIME_LIMIT = 30 * 60 # 30 min
MEMORY_LIMIT = 3584 # 3584M


ENVIRONMENT = TetralithEnvironment(
    email="daniel.gnad@liu.se",
#    time_limit_per_task="24:00:00",
#    memory_per_cpu="8300M",
    extra_options="#SBATCH -A naiss2024-5-404", # parground
#    extra_options="#SBATCH -A naiss2023-5-314", # dfsplan
)

exp = Experiment(environment=ENVIRONMENT)

SUITE = common_setup.DEFAULT_SATISFICING_SUITE

exp.add_resource("solver", "/proj/parground/users/x_dangn/madagascar/MpC")

common_options = ["-r", TIME_LIMIT, "-m", MEMORY_LIMIT, "-Q", "-o", "sas_plan"]

for name, config in CONFIGS:
    for task in suites.build_suite(BENCHMARKS_DIR, SUITE):
        run = exp.add_run()
        run.add_resource("domain", task.domain_file, "domain.pddl", symlink=True)
        run.add_resource("problem", task.problem_file, "problem.pddl", symlink=True)
        run.add_command(
            "planner",
            ["{solver}"] + config + common_options + ["{domain}", "{problem}"],
            time_limit=TIME_LIMIT,
            memory_limit=MEMORY_LIMIT,
        )
        run.add_command(
            "validate",
            ["validate", "{domain}", "{problem}", "sas_plan"],
            memory_limit=MEMORY_LIMIT,
        )
        run.set_property("domain", task.domain)
        run.set_property("problem", task.problem)
        run.set_property("algorithm", name)
        run.set_property("component_options", config)
        run.set_property("driver_options", common_options)
        run.set_property("time_limit", TIME_LIMIT)
        run.set_property("memory_limit", MEMORY_LIMIT * 1000)
        run.set_property("id", [name, task.domain, task.problem])


exp.add_parser(madagascar_parser.MadagascarParser())

exp.add_step('build', exp.build)
exp.add_step('start', exp.start_runs)
exp.add_step("parse", exp.parse)

exp.add_fetcher(name='fetch')

common_setup.add_compress_and_delete_runs_step(exp)


FORMAT = "html"

# REPORT TABLES
attributes = common_setup.ATTRIBUTES

exp.add_report(AbsoluteReport(attributes=attributes, filter=[filters.filter_madagascar_known_unexplained_errors]), outfile=f"{SCRIPT_NAME}-all.html")



# SCATTER PLOTS

PLOT_FORMAT = "png"

#for c1, c2 in [(f"{REVISION}-Esat", f"{REVISION}-Esat-LP-F0.2s1M-clo")]:
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

exp.run_steps()


