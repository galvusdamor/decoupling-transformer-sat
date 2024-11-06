from collections import defaultdict
from lab.reports import geometric_mean, arithmetic_mean



class VirtualSat:
    def __init__(self, replace_configs, time_limit, base_names=["sat"]):
        assert all(any(c.startswith(b) and c != b and not c.startswith(f"{b}-") for b in base_names) for c in replace_configs)
        self.base_names = base_names
        self.replace_configs = replace_configs
        self.time_limit = time_limit
        self.time_limit_per_run = 60 * 5
        self.runs_per_inst_per_config_per_iteration = defaultdict(lambda: defaultdict(list))
        self.number_unsolved_overall_with_some_solved = defaultdict(int)
        self.max_iteration_solved = defaultdict(int)
        self.max_planner_time_iteration_solved = defaultdict(float)
        self.config_ext = "inc"

    def get_config_name_extension(self):
        return self.config_ext

    def get_run_length_and_factoring(run, base_name):
        alg = run["algorithm"]
        parts = alg.split("-", 1)
        length = int(parts[0][len(base_name):])
        if len(parts) == 1:
            # config is something like satXX
            return length, ""
        else:
            # config is something like satXX-factoring
            return length, parts[1]

    def get_base_name(self, alg):
        for base_name in self.base_names:
            if alg.startswith(base_name) and alg != base_name and not alg.startswith(f"{base_name}-"):
                return base_name
        return None

    def add_run(self, run):
        base_name = self.get_base_name(run["algorithm"])
        if base_name:
            length, factoring = VirtualSat.get_run_length_and_factoring(run, base_name)
            config_name = f"{base_name}_{factoring}"
            inst = f"{run['domain']}:{run['problem']}"
            while len(self.runs_per_inst_per_config_per_iteration[inst][config_name]) <= length:
                self.runs_per_inst_per_config_per_iteration[inst][config_name].append(None)
            self.runs_per_inst_per_config_per_iteration[inst][config_name][length] = run
        return run

    def cleanup_run(self, run, attributes_to_delete):
        # cleanup run information
        for attr in attributes_to_delete:
            # better don't show this info instead of showing wrong info
            if attr in run:
                del run[attr]

    def replace_config(self, run):
        if run["algorithm"] in self.replace_configs:
                    
            attributes_to_delete = ["planner_time", "planner_memory", "cost", "search_time", "total_time", "memory"]
            
            base_name = self.get_base_name(run['algorithm'])
            _, factoring = VirtualSat.get_run_length_and_factoring(run, base_name)
            config_name = f"{base_name}_{factoring}"
            new_config_name = f"{base_name}-{self.config_ext}-{factoring}" if factoring else f"{base_name}-{self.config_ext}"
            run["algorithm"] = new_config_name

            inst = f"{run['domain']}:{run['problem']}"

            runs = self.runs_per_inst_per_config_per_iteration[inst][config_name]

            if all(r["coverage"] == 0 for r in runs):
                run["error"] = "search-unsolvable-incomplete"
                run["coverage"] = 0
                self.cleanup_run(run, attributes_to_delete)
                return run

            translate_time = -1
            sat_prep_time = -1
            for r in runs:
                if translate_time == -1 and "translator_time_done" in r:
                    translate_time = r["translator_time_done"]
                    if sat_prep_time != -1:
                        break
                if sat_prep_time == -1 and "sat_preprocessing_time" in r:
                    sat_prep_time = r["sat_preprocessing_time"]
                    if translate_time != -1:
                        break
            if sat_prep_time < 0:
                sat_prep_time = 0.01
            assert translate_time >= 0
            assert sat_prep_time >= 0, runs

            time_until_search = translate_time + sat_prep_time
            sum_time = time_until_search
            coverage = 0
            solved_run = None
            for length, r in enumerate(runs):
                sat_prep_time_r = r["sat_preprocessing_time"] if "sat_preprocessing_time" in r else sat_prep_time
                if r["coverage"] == 1:
                    if r["translator_time_done"] + r["total_time"] > self.time_limit_per_run:
                        sum_time += self.time_limit_per_run
                    else:
                        sum_time += max(0.0, r["total_time"] - sat_prep_time_r)
                        if sum_time <= self.time_limit:
                            length_iteration_solved = length
                            coverage = 1
                            solved_run = r
                            run["total_time_solved_iteration"] = r["total_time"]
                        break
                else:
                    if r["planner_wall_clock_time"] > self.time_limit_per_run:
                        sum_time += self.time_limit_per_run
                    else:
                        translate_time_r = r["translator_time_done"] if "translator_time_done" in r else translate_time
                        time_until_search_r = translate_time_r + sat_prep_time_r
                        sum_time += max(0.0, r["planner_wall_clock_time"] - time_until_search_r)
                if sum_time > self.time_limit:
                    break

            if coverage == 1:
                run["error"] = "success"
                run["coverage"] = 1
                time_without_validation = solved_run["translator_time_done"] + solved_run["total_time"]
                run["planner_time_iteration_solved"] = time_without_validation
                run["planner_time"] = sum_time
                run["total_time"] = sum_time - translate_time
                run["length_iteration_solved"] = length_iteration_solved
                for attr in ["cost", "planner_memory"]:
                    run[attr] = solved_run[attr]
                attributes_to_delete = ["search_time", "memory"]
                self.cleanup_run(run, attributes_to_delete)
                self.max_iteration_solved[new_config_name] = max(self.max_iteration_solved[new_config_name], length_iteration_solved)
                self.max_planner_time_iteration_solved[new_config_name] = max(self.max_planner_time_iteration_solved[new_config_name], time_without_validation)
            else:
                self.cleanup_run(run, attributes_to_delete)
                run["error"] = "search-out-of-time"
                run["coverage"] = 0
                self.number_unsolved_overall_with_some_solved[new_config_name] += 1
        return run

    def print_statistics(self):
        for config, num_unsolved in self.number_unsolved_overall_with_some_solved.items():
            print(f"Max solved iteration of config {config}: {self.max_iteration_solved[config]}")
            print(f"Max planner time iteration solved of config {config}: {self.max_planner_time_iteration_solved[config]}")
            print(f"Number of Instanzes not solved overall, but by some bound for config {config}: {num_unsolved}")

class VirtualSatRoundRobin:
    def __init__(self, replace_configs, time_limit, memory_limit, base_names=["sat"]):
        assert all(any(c.startswith(b) and c != b and not c.startswith(f"{b}-") for b in base_names) for c in replace_configs)
        self.base_names = base_names
        self.replace_configs = replace_configs
        self.time_limit = time_limit
        self.time_limit_per_run = 300
        self.memory_limit = memory_limit
        self.runs_per_inst_per_config_per_iteration = defaultdict(lambda: defaultdict(list))
        self.number_unsolved_overall_with_some_solved = defaultdict(int)
        self.max_iteration_solved = defaultdict(int)
        self.max_planner_time_iteration_solved = defaultdict(float)
        self.config_ext = "RR"

    def get_config_name_extension(self):
        return self.config_ext

    def get_run_length_and_factoring(run, base_name):
        alg = run["algorithm"]
        parts = alg.split("-", 1)
        length = int(parts[0][len(base_name):])
        if len(parts) == 1:
            # config is something like satXX
            return length, ""
        else:
            # config is something like satXX-factoring
            return length, parts[1]

    def get_base_name(self, alg):
        for base_name in self.base_names:
            if alg.startswith(base_name) and alg != base_name and not alg.startswith(f"{base_name}-"):
                return base_name
        return None

    def add_run(self, run):
        base_name = self.get_base_name(run["algorithm"])
        if base_name:
            length, factoring = VirtualSatRoundRobin.get_run_length_and_factoring(run, base_name)
            config_name = f"{base_name}_{factoring}"
            inst = f"{run['domain']}:{run['problem']}"
            while len(self.runs_per_inst_per_config_per_iteration[inst][config_name]) <= length:
                self.runs_per_inst_per_config_per_iteration[inst][config_name].append(None)
            self.runs_per_inst_per_config_per_iteration[inst][config_name][length] = run
        return run

    def cleanup_run(self, run, attributes_to_delete):
        # cleanup run information
        for attr in attributes_to_delete:
            # better don't show this info instead of showing wrong info
            if attr in run:
                del run[attr]

    def replace_config(self, run):
        if run["algorithm"] in self.replace_configs:
            base_name = self.get_base_name(run['algorithm'])
            _, factoring = VirtualSatRoundRobin.get_run_length_and_factoring(run, base_name)
            config_name = f"{base_name}_{factoring}"
            new_config_name = f"{base_name}-{self.config_ext}-{factoring}" if factoring else f"{base_name}-{self.config_ext}"
            run["algorithm"] = new_config_name 
            inst = f"{run['domain']}:{run['problem']}"

            runs = self.runs_per_inst_per_config_per_iteration[inst][config_name]

            attributes_to_delete = ["search_time", "memory"]
           
            if all(r["coverage"] == 0 for r in runs):
                if any(r["error"] == "translate-out-of-memory" for r in runs):
                    run["error"] = "translate-out-of-memory"
                elif all(r["error"] == "search-out-of-memory" for r in runs):
                    run["error"] = "search-out-of-memory"
                else:
                    run["error"] = "search-unsolvable-incomplete"
                attributes_to_delete += ["cost", "total_time", "planner_time", "planner_memory"]
                self.cleanup_run(run, attributes_to_delete)
                return run

            translate_time = -1
            sat_prep_time = -1
            for r in runs:
                if translate_time == -1 and "translator_time_done" in r:
                    translate_time = r["translator_time_done"]
                    if sat_prep_time != -1:
                        break
                if sat_prep_time == -1 and "sat_preprocessing_time" in r:
                    sat_prep_time = r["sat_preprocessing_time"]
                    if translate_time != -1:
                        break
            assert translate_time >= 0
            assert sat_prep_time >= 0

            time_until_search = translate_time + sat_prep_time 
            sum_time = time_until_search
            solved_run = None

            time_inc = 1
            max_unsolved = -1
            time_per_config = []
            max_parallel_configs = 0 # TODO always have as many configs in parallel as fit into memory
            used_memory = 0
            progress = True

            def update_memory_and_max_parallel_configs(used_memory, max_unsolved, max_parallel_configs, runs, memory_limit):
                while used_memory <= memory_limit and max_unsolved + max_parallel_configs + 1 < len(runs):
                    max_parallel_configs += 1
                    used_memory += min(runs[max_unsolved + max_parallel_configs]["raw_memory"], memory_limit - 10)
                if used_memory > memory_limit:
                    used_memory -= min(runs[max_unsolved + max_parallel_configs]["raw_memory"], memory_limit - 10)
                    max_parallel_configs -= 1                                                                         


            while not solved_run and sum_time < self.time_limit and progress:
                progress = False
                update_memory_and_max_parallel_configs(used_memory, max_unsolved, max_parallel_configs, runs, self.memory_limit)
                length = max_unsolved
                while length < min(max_unsolved + 1 + max_parallel_configs, len(runs)):
                    length += 1
                    r = runs[length]
                    while len(time_per_config) <= length:
                        time_per_config += [59.0] # time given to first iteration
                    time_per_config[length] += time_inc
                    if time_per_config[length] >= self.time_limit_per_run + time_inc:
                        continue
                    if r["coverage"] == 1:
                        if r["total_time"] - r["sat_preprocessing_time"] <= time_per_config[length]:
                            solved_run = r
                            length_iteration_solved = length
                            sum_time += r["total_time"]
                            run["total_time_solved_iteration"] = r["total_time"]
                            break
                    elif r["error"] == "error-search-unsolvable-incomplete":
                        if r["planner_wall_clock_time"] - time_until_search <= time_per_config[length]:
                            max_unsolved = max(max_unsolved, length)
                            used_memory -= min(runs[length]["raw_memory"], self.memory_limit - 10)
                            update_memory_and_max_parallel_configs(used_memory, max_unsolved, max_parallel_configs, runs, self.memory_limit)
                    elif r["planner_wall_clock_time"] - time_until_search <= time_per_config[length]:
                        # don't increase sum_time if config ran oom or crashed faster than its time_per_config
                        used_memory -= min(runs[length]["raw_memory"], self.memory_limit - 10)
                        update_memory_and_max_parallel_configs(used_memory, max_unsolved, max_parallel_configs, runs, self.memory_limit)
                        continue
                    progress = True
                    sum_time += time_inc

            
            if solved_run:
                run["error"] = "success"
                run["coverage"] = 1
                time_without_validation = solved_run["translator_time_done"] + solved_run["total_time"]
                run["planner_time_iteration_solved"] = time_without_validation
                run["planner_time"] = sum_time
                run["total_time"] = sum_time - time_until_search
                for attr in ["cost", "planner_memory"]:
                    run[attr] = solved_run[attr]
                run["length_iteration_solved"] = length_iteration_solved
                self.max_iteration_solved[new_config_name] = max(self.max_iteration_solved[new_config_name], length_iteration_solved)
                self.max_planner_time_iteration_solved[new_config_name] = max(self.max_planner_time_iteration_solved[new_config_name], time_without_validation)
            else:
                run["error"] = "search-out-of-time"
                run["coverage"] = 0
                self.number_unsolved_overall_with_some_solved[new_config_name] += 1
                attributes_to_delete += ["cost", "total_time", "planner_time", "planner_memory"]

            self.cleanup_run(run, attributes_to_delete)
          
        return run

    def print_statistics(self):
        for config, num_unsolved in self.number_unsolved_overall_with_some_solved.items():
            print(f"Max solved iteration of config {config}: {self.max_iteration_solved[config]}")
            print(f"Max planner time iteration solved of config {config}: {self.max_planner_time_iteration_solved[config]}")
            print(f"Number of Instanzes not solved overall, but by some bound for config {config}: {num_unsolved}")


class NonDecoupledTaskFilter:
    def __init__(self, reference_configs=None):
        self.decoupled_tasks = defaultdict(set)
        self.factoring_not_possible_tasks = defaultdict(set)
        self.maybe_not_possible_tasks = defaultdict(set)

        self.unsupported_tasks = defaultdict(set)
        self.translate_oom_tasks = defaultdict(set)

        self.reference_configs = reference_configs

    def add_runs(self, run):
        domain = run["domain"]
        problem = run["problem"]
        if run["error"] == "search-unsupported":
            self.unsupported_tasks[domain].add(problem)
        if run["error"] == "translate-out-of-memory":
            self.translate_oom_tasks[domain].add(problem)
        if self.reference_configs and run["algorithm"] not in self.reference_configs:
            return run
        if "number_leaf_factors" in run and run["number_leaf_factors"] > 0:
            self.decoupled_tasks[domain].add(problem)
        elif ("is_lp_factoring" in run and run["is_lp_factoring"] == 1) or ("is_miura_factoring" in run and run["is_miura_factoring"] == 1):
            self.maybe_not_possible_tasks[domain].add(problem)
        if "factoring_possible" in run and run["factoring_possible"] == 0:
            self.factoring_not_possible_tasks[domain].add(problem) 
        return run

    def filter_non_decoupled_runs(self, run):
        problem = run["problem"]
        domain = run["domain"]
        if problem in self.unsupported_tasks[domain]:
            return False 
        if problem in self.translate_oom_tasks[domain]:
            return False
        if problem in self.factoring_not_possible_tasks[domain]:
            return False
        if problem in self.maybe_not_possible_tasks[domain] and problem not in self.decoupled_tasks[domain]:
            return False
        return run

    def print_statistics(self):
        print(f"Number instances where factoring is not possible: {sum(len(tasks) for tasks in self.factoring_not_possible_tasks.values())}")
        print(f"Number instances where factoring was found: {sum(len(tasks) for tasks in self.decoupled_tasks.values())}")
        print(f"Number instances where factoring may not be possible: {sum(len(tasks) for tasks in self.maybe_not_possible_tasks.values())}")
        print(f"Number unsupported instances: {sum(len(tasks) for tasks in self.unsupported_tasks.values())}")


class CompactCoverageFilter():
    def __init__(self, configs):
        self.coverage = defaultdict(lambda : defaultdict(int))
        self.configs = configs
    def add_run(self, run):
        if run["algorithm"] not in self.configs:
            return run
        if run["coverage"] == 1:
            self.coverage[run["algorithm"]][run["domain"]] += 1
        return run
    def set_compact_coverage(self, run):
        run["compact_coverage"] = run["coverage"]
        if all(self.coverage[list(self.coverage.keys())[0]][run["domain"]] == self.coverage[alg][run["domain"]] for alg in self.coverage.keys()):
            run["problem"] = run["domain"] + run["problem"]
            run["domain"] = "zzOther"
        return run

def remove_revision(run):
    if len(run["algorithm"]) > 40:
        run["algorithm"] = run["algorithm"][41:]
    return run

def filter_kissat_oom(run):
    if "unexplained_errors" in run:
        if any("kissat: fatal error: out-of-memory" in x for x in run["unexplained_errors"]):
            del run["unexplained_errors"]
            run["error"] = "search-out-of-memory"
    return run

def filter_madagascar_cost_warning(run):
    if "unexplained_errors" in run:
        run["unexplained_errors"] = [line for line in run["unexplained_errors"] if not "ERROR: Could not allocate more memory" in line]
    return run

def filter_madagascar_out_of_memory_error(run):
    if "unexplained_errors" in run:
        run["unexplained_errors"] = [line for line in run["unexplained_errors"] if not "WARNING: will ignore action costs" in line]
    return run

def filter_madagascar_known_unexplained_errors(run):
    run1 = filter_madagascar_cost_warning(run)
    run2 = filter_madagascar_out_of_memory_error(run1)
    return run2
