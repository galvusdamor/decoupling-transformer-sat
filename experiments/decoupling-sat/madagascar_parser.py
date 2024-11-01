#! /usr/bin/env python

import re

from lab.parser import Parser

def adjust_planner_memory(props):
    assert "planner_memory_mb" in props or "planner_memory_gb" in props
    if "planner_memory_mb" in props:
        # Madagascar's output is in MB, the default in lab reports is Kbytes
        props["planner_memory"] = int(props["planner_memory_mb"] * 1000)
    elif "planner_memory_gb" in props:
        # Madagascar's output is in GB, the default in lab reports is Kbytes
        props["planner_memory"] = int(props["planner_memory_gb"] * 1000 * 1000)

    
def set_planner_error_and_coverage(content, props):
    # NOTE: on timeout, exit code is 0, on out of memory it's 1
    props["coverage"] = int("steps" in props)

    if "oom_memory_attention" in props:
        assert props["coverage"] == 0
        props["error"] = "search-out-of-memory"

    if "oom_memory_error" in props:
        assert props["coverage"] == 0
        props["error"] = "search-out-of-memory"

    if "oot_time" in props:
        assert props["coverage"] == 0
        assert "error" not in props
        props["error"] = "search-out-of-time"

    if "unsolved_steps" in props:
        assert props["coverage"] == 0
        assert "error" not in props
        props["error"] = "search-unsolvable"

    if "error" not in props:
        if "Was not allowed to increase horizon length. Exiting.." in content:
            assert props["coverage"] == 0
            props["error"] = "search-probably-out-of-memory"    

    if props["coverage"] == 1:
        assert props["validate_exit_code"] == 0
        props["error"] = "success"
        adjust_planner_memory(props)
    else:
        # make sure we have not accidentally parsed something.. memory is being printed, though, and runtime as well if the task is proved unsolvable
        assert all(x not in props for x in ['steps', 'plan_length', 'cost']), str(props) + str(content)
        if "error" not in props:
            props["error"] = "search-unsolvable-incomplete"


class MadagascarParser(Parser):
    def __init__(self):
        Parser.__init__(self)

        self.add_pattern('steps', 'PLAN FOUND: (.+) steps', required=False, type=int)
        self.add_pattern('plan_length', '(.+) actions in the plan.', required=False, type=int)
        self.add_pattern('cost', 'Cost of the plan is (.+).', required=False, type=int)
        self.add_pattern('planner_time', 'total time (.+) preprocess', required=False, type=float)
        self.add_pattern('planner_memory_mb', 'total size (.+) MB', required=False, type=float)
        self.add_pattern('planner_memory_gb', 'total size (.+) GB', required=False, type=float)

        self.add_pattern('unsolved_steps', "PLAN NOT FOUND: steps (.+) tested", required=False, type=str)
        self.add_pattern('oom_memory_attention', "ATTENTION: Memory bound (.+) MB reached,", required=False, type=float)
        self.add_pattern('oot_time', "Timeout after (.+) seconds of real time.", required=False, type=float)
        self.add_pattern('oom_memory_error', "ERROR: Could not allocate more memory (.+).", required=False, type=float, file="run.err")
         
        self.add_pattern("node", r"node: (.+)\n", type=str, file="driver.log", required=True)
        self.add_pattern("planner_exit_code", r"planner exit code: (.+)\n", type=int, file="driver.log")
        self.add_pattern("validate_exit_code", r"validate exit code: (.+)\n", type=int, file="driver.log")

        self.add_function(set_planner_error_and_coverage)

