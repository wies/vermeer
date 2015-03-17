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

# phase 2: create data for plots

print("\\begin{tikzpicture}")
print("\\begin{axis}[xlabel={$T_{\\text{meas}}$}, ylabel={$T_{\\text{cal}}$}]")
print("\\addplot[scatter, only marks, scatter src=\\thisrow{class}, error bars/.cd, y dir=both, x dir=both, y explicit, x explicit, error bar style={color=mapped color}] table[x=x,y=y] {")
print("x y class")

dataset0 = datasets[0]
dataset1 = datasets[1]
trace_idx0 = dataset0.indices["Trace"]
trace_idx1 = dataset1.indices["Trace"]
reduced_stmts_idx0 = dataset0.indices["Reduced-Stmts"]
reduced_stmts_idx1 = dataset1.indices["Reduced-Stmts"]
for benchmark_name in dataset0.dataset.keys():
  traces0 = dataset0.dataset[benchmark_name]
  traces1 = dataset1.dataset[benchmark_name]
  # let's be quadratic for now
  for trace0 in traces0:
    for trace1 in traces1:
      if trace0[trace_idx0] == trace1[trace_idx1]:
        print(trace0[reduced_stmts_idx0] + " " + trace1[reduced_stmts_idx1] + " 0")
        break

print("};")
print("\\end{axis}")
print("\\end{tikzpicture}")
