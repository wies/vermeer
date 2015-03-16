import os
import sys

def set_from_datafile(datafile_name):
  benchmarks = []
  with open(datafile_name, "r") as datafile:
    for line in datafile:
      if not(line.startswith("#")):
        dataitems = line.split(",")
        benchmarks.append((dataitems[0], dataitems[1]))
  return set(benchmarks)

with open("datafiles.txt", "r") as datafile_names:
  sets = []
  for datafile_name_line in datafile_names:
    datafile_name = datafile_name_line.rstrip()
    myset = set_from_datafile(datafile_name)
    sets.append(myset)
  intersection = sets.pop()
  for benchmark_set in sets:
    intersection.intersection_update(benchmark_set)
  for benchmark in intersection:
    print(benchmark)

