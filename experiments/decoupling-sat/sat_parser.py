#! /usr/bin/env python

import re

from lab.parser import Parser


def add_sat_preprocessing_time(content, props):
    if "total_time_until_disabling_graph" in props:
        props["sat_preprocessing_time"] = props["total_time_until_disabling_graph"]
    elif "total_time_until_first_formula" in props:
        props["sat_preprocessing_time"] = props["total_time_until_first_formula"]
    #else:
    #    assert props["error"] in ["translate-out-of-memory", "search-unsolvable-incomplete"] or "unexplained_errors" in props, content +str(props)

def parse_last_sat_plan_steps(content, props):
    matches = re.findall(r"Building SAT formula for plan length (.+)", content)
    if matches:
        props["sat_plan_steps"] = int(matches[-1])

class SATParser(Parser):
    def __init__(self):
        Parser.__init__(self)
        self.add_pattern('number_disabling_graph_sccs', 'Disabling Graph contains (.+) SCCS.', required=False, type=int)
        self.add_pattern('total_time_until_disabling_graph', '\[t=(.+)s, .+ KB\] Disabling Graph contains', required=False, type=float) # for encoding=2
        self.add_pattern('total_time_until_first_formula', '\[t=(.+)s, .+ KB\] Other SCCS:', required=False, type=float) # for encoding=0 (but also in log for encoding=2!)

        #self.add_pattern('sat_plan_steps', 'Building SAT formula for plan length (.+)', required=False, type=int)

        self.add_pattern('number_sccs', 'Number of SCCs (.+)', required=False, type=int)
        self.add_pattern('number_size_1_sccs', 'Size 1 SCCS: (.+)', required=False, type=int)
        self.add_pattern('number_implication_sccs', 'Implication SCCS: (.+)', required=False, type=int)
        self.add_pattern('number_onefact_sccs', 'OneFact SCCS: (.+)', required=False, type=int)
        self.add_pattern('number_onevar_sccs', 'OneVar SCCS: (.+)', required=False, type=int)
        self.add_pattern('number_onefact_internal_sccs', 'OneFact internal SCCS: (.+)', required=False, type=int)
        self.add_pattern('number_onevar_internal_sccs', 'OneVar internal SCCS: (.+)', required=False, type=int)
        self.add_pattern('number_other_sccs', 'Other SCCS: (.+)', required=False, type=int)

        for type in ["sizeone", "problematic-2ante", "implication", "onefact", "onefactinternal", "onevar", "onevarinternal", "problematic-general"]:
            self.add_pattern(f'number_{type}_sccs',      f"KB\] {type} number_sccs: (.+) minsize:", required=False, type=int)
            self.add_pattern(f'min_size_{type}_sccs',    f"KB\] {type} number_sccs: .+ minsize: (.+) maxsize:", required=False, type=int)
            self.add_pattern(f'max_size_{type}_sccs',    f"KB\] {type} number_sccs: .+ minsize: .+ maxsize: (.+) sumsize:", required=False, type=int)
            self.add_pattern(f'sum_size_{type}_sccs',    f"KB\] {type} number_sccs: .+ minsize: .+ maxsize: .+ sumsize: (.+) percent_of_all:", required=False, type=int)
            self.add_pattern(f'percentage_{type}_sccs',  f"KB\] {type} number_sccs: .+ minsize: .+ maxsize: .+ sumsize: .+ percent_of_all: (.+) median:", required=False, type=float)
            self.add_pattern(f'median_size_{type}_sccs', f"KB\] {type} number_sccs: .+ minsize: .+ maxsize: .+ sumsize: .+ percent_of_all: .+ median: (.+) average:", required=False, type=float)
            self.add_pattern(f'avg_size_{type}_sccs',    f"KB\] {type} number_sccs: .+ minsize: .+ maxsize: .+ sumsize: .+ percent_of_all: .+ median: .+ average: (.+)", required=False, type=float)

        self.add_pattern('number_statically_true_dvars',     "KB\] statically_true number: (.+) percent_of_all:", required=False, type=int)
        self.add_pattern('percentage_statically_true_dvars', "KB\] statically_true number: .+ percent_of_all: (\d+\.*\d*)", required=False, type=float)

        self.add_function(add_sat_preprocessing_time)       
        self.add_function(parse_last_sat_plan_steps)
