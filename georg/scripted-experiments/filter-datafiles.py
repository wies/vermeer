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

# phase 1: determine the set of common benchmarks
def get_common_benchmarks():
  with open("datafiles.txt", "r") as datafile_names:
    sets = []
    for datafile_name_line in datafile_names:
      datafile_name = datafile_name_line.rstrip().split(' ')
      myset = set_from_datafile(datafile_name[0])
      sets.append(myset)
    intersection = sets.pop()
    for benchmark_set in sets:
      intersection.intersection_update(benchmark_set)
    return intersection

#phase 2: remove uncommon benchmarks from datafiles
def filter_benchmark(dat_file_name, new_dat_file_name, benchmarks):
  with open(dat_file_name, "r") as datafile:
    with open(new_dat_file_name, "w") as new_datafile:
      for original_line in datafile:
        if original_line.startswith("#"):
          new_datafile.write(original_line)
        else:
          dataitems = original_line.split(",")
          if (dataitems[0], dataitems[1]) in benchmarks:
            new_datafile.write(original_line)
          
def filter_benchmarks(benchmarks):
  with open("datafiles.txt", "r") as datafile_names:
    for datafile_name_line in datafile_names:
      datafile_name = datafile_name_line.rstrip().split(' ')
      filter_benchmark(datafile_name[0], datafile_name[1], benchmarks)

benchmarks = get_common_benchmarks()
filter_benchmarks(benchmarks)


