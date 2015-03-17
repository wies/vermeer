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

# phase 1: collect data
field0 = sys.argv[1]
field1 = sys.argv[2]
datasets = []
for i in range(3, len(sys.argv)):
  datasets.append(read_dataset(sys.argv[i]))

# phase 2: create data for plots
print_lines = []
dataset0 = datasets[0]
dataset1 = datasets[1]
trace_idx0 = dataset0.indices["Trace"]
trace_idx1 = dataset1.indices["Trace"]
reduced_stmts_idx0 = dataset0.indices[field0]
reduced_stmts_idx1 = dataset1.indices[field1]
xs = []
ys = []
for benchmark_name in dataset0.dataset.keys():
  traces0 = dataset0.dataset[benchmark_name]
  traces1 = dataset1.dataset[benchmark_name]
  # let's be quadratic for now
  for trace0 in traces0:
    for trace1 in traces1:
      if trace0[trace_idx0] == trace1[trace_idx1]:
        v0 = int(trace0[reduced_stmts_idx0])
        v1 = int(trace1[reduced_stmts_idx1])
        xs.append(v0)
        ys.append(v1)
        print_lines.append(trace0[reduced_stmts_idx0] + " " + trace1[reduced_stmts_idx1] + " 0")
        break

if min(xs) > min(ys):
  axis_min = min(ys) - 1
else:
  axis_min = min(xs) - 1

if (axis_min > 0):
  axis_min = 0

if max(xs) < max(ys):
  axis_max = max(ys) + 1
else:
  axis_max = max(xs) + 1

print("\\begin{tikzpicture}")
print("\\begin{axis}[xmin=" + str(axis_min) + ", xmax=" + str(axis_max) + ", ymin=" + str(axis_min) + ", ymax=" + str(axis_max) + ",xlabel={" + field0 + "}, ylabel={" + field1 + "}]")
print("\\addplot[scatter, only marks, scatter src=\\thisrow{class}, error bars/.cd, y dir=both, x dir=both, y explicit, x explicit, error bar style={color=mapped color}] table[x=x,y=y] {")
print("x y class")

for line in print_lines:
  print(line)

print("};")
print("\\end{axis}")
print("\\end{tikzpicture}")
