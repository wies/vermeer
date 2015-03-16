import os
import sys
import math

class DataSet:
  def __init__(self):
    self.dataset = dict()
    self.indices = dict()

class Stats:
  def __init__(self):
    self.stats_cs = dict()
    self.stats_stmts = dict()
    self.stats_vars = dict()
    self.stats_counter = dict()

def read_dataset(datafile_name):
  dataset = DataSet()
  with open(datafile_name, "r") as datafile:
    for line in datafile:
      if not(line.startswith("#")):
        dataitems = line.rstrip().split(",")
        key = dataitems[0]
        if key in dataset.dataset:
          dataset.dataset[key].append(dataitems)
        else:
          dataset.dataset[key] = [ dataitems ]
      else:
        if line.startswith("# Format: "):
          # calculate indices
          items = line.rstrip()[10:].split(",")
          for i in range(0, len(items)):
            dataset.indices[items[i]] = i
  return dataset

def reduction_fraction(old, new):
  return ((float(old)-float(new))/float(old))

def calculate_stats(dataset):
  config_stats = Stats()
  benchmark_name_idx = dataset.indices["Benchmark"]
  trace_idx = dataset.indices["Trace"]
  initial_css_idx = dataset.indices["Initial-CSs"]
  initial_stmts_idx = dataset.indices["Initial-Stmts"]
  initial_vars_idx = dataset.indices["Initial-Vars"]
  reduced_css_idx = dataset.indices["Reduced-CSs"]
  reduced_stmts_idx = dataset.indices["Reduced-Stmts"]
  reduced_vars_idx = dataset.indices["Reduced-Vars"]
  for benchmark in dataset.dataset.iteritems():
    key = benchmark[benchmark_name_idx]
    traces = benchmark[trace_idx]
    for trace in traces:
      reduction_cs = reduction_fraction(trace[initial_css_idx], trace[reduced_css_idx])
      reduction_stmts = reduction_fraction(trace[initial_stmts_idx], trace[reduced_stmts_idx])
      reduction_vars = reduction_fraction(trace[initial_vars_idx], trace[reduced_vars_idx])
      if key in config_stats.stats_cs:
        config_stats.stats_cs[key] += reduction_cs
        config_stats.stats_stmts[key] += reduction_stmts
        config_stats.stats_vars[key] += reduction_vars
        config_stats.stats_counter[key] += 1
      else:
        config_stats.stats_cs[key] = reduction_cs
        config_stats.stats_stmts[key] = reduction_stmts
        config_stats.stats_vars[key] = reduction_vars
        config_stats.stats_counter[key] = 1
  return config_stats

def percentage(fraction):
  return int(math.floor(0.5 + 100*(fraction)))

# phase 1: collect data
datasets = []
for i in range(1, len(sys.argv)):
  datasets.append(read_dataset(sys.argv[i]))

# phase 2: calculate statistics
stats = []
for dataset in datasets:
  stats.append(calculate_stats(dataset))
results = []
for i in range(0, len(stats)):
  stat = stats[i] # for each configuration we have one stat
  result = dict()
  for benchmark_name in stat.stats_cs.keys():
    nr_of_traces = stat.stats_counter[benchmark_name]
    sum_of_fractions_cs = stat.stats_cs[benchmark_name]
    sum_of_fractions_stmts = stat.stats_stmts[benchmark_name]
    sum_of_fractions_vars = stat.stats_vars[benchmark_name]
    # calculate the means:
    avg_red_cs_fraction = sum_of_fractions_cs/nr_of_traces
    avg_red_stmts_fraction = sum_of_fractions_stmts/nr_of_traces
    avg_red_vars_fraction = sum_of_fractions_vars/nr_of_traces
    # calculate the deviation:
    dataset = datasets[i]
    benchmark = dataset.dataset[benchmark_name]
    dev_cs = 0
    dev_stmts = 0
    dev_vars = 0
    initial_css_idx = dataset.indices["Initial-CSs"]
    initial_stmts_idx = dataset.indices["Initial-Stmts"]
    initial_vars_idx = dataset.indices["Initial-Vars"]
    reduced_css_idx = dataset.indices["Reduced-CSs"]
    reduced_stmts_idx = dataset.indices["Reduced-Stmts"]
    reduced_vars_idx = dataset.indices["Reduced-Vars"]
    for trace in benchmark:
      reduction_cs = reduction_fraction(trace[initial_css_idx], trace[reduced_css_idx])
      delta_cs = reduction_cs - avg_red_cs_fraction
      dev_cs += delta_cs * delta_cs
      reduction_stmts = reduction_fraction(trace[initial_stmts_idx], trace[reduced_stmts_idx])
      delta_stmts = reduction_stmts - avg_red_stmts_fraction
      dev_stmts += delta_stmts * delta_stmts
      reduction_vars = reduction_fraction(trace[initial_vars_idx], trace[reduced_vars_idx])
      delta_vars = reduction_vars - avg_red_vars_fraction
      dev_vars += delta_vars * delta_vars
    dev_cs /= nr_of_traces
    dev_cs = math.sqrt(dev_cs)
    dev_stmts /= nr_of_traces
    dev_stmts = math.sqrt(dev_stmts)
    dev_vars /= nr_of_traces
    dev_vars = math.sqrt(dev_vars)
    result[benchmark_name] = (avg_red_cs_fraction, dev_cs, avg_red_stmts_fraction, dev_stmts, avg_red_vars_fraction, dev_vars)
  results.append(result)

# phase 3: write benchmark name and number of traces
config_stats = stats[0]
str_representation = dict()
for s in config_stats.stats_cs.iteritems():
  str_representation[s[0]] = (s[0] + " & " + str(config_stats.stats_counter[s[0]]))

for result in results:
  for benchmark_name in result.keys():
    str_representation[benchmark_name] += " & " + str(percentage(result[benchmark_name][0])) + " & " + str(percentage(result[benchmark_name][1])) + " & " + str(percentage(result[benchmark_name][2])) + " & " + str(percentage(result[benchmark_name][3])) + " & " + str(percentage(result[benchmark_name][4])) + " & " + str(percentage(result[benchmark_name][5]))

keys = list(str_representation.keys())
keys.sort()
for key in keys:
  s = str_representation[key]
  print(s + "\\\\")


