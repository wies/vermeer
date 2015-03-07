import sys
import os
import glob
import subprocess

class DataEntry:
  def __init__(self, category, nr_context_switches, nr_statements, nr_variables):
    self.category = category
    self.nr_context_switches = nr_context_switches
    self.nr_statements = nr_statements
    self.nr_variables = nr_variables

class DataSet:
  def __init__(self, benchmark, trace_file, data_entry_list):
    self.benchmark = benchmark
    self.trace_file = trace_file
    self.data_entry_list = data_entry_list

cwd = os.getcwd()
vermeer = os.environ['VERMEER_PATH'] + "/cil-1.7.3/bin/cilly"
options = "--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=allthreads --smtcalcstats --flowsensitive"

with open("directories.txt", "r") as f:
  data_set_list = []
  for line in f:
    directory = line.strip()
    sys.stdout.write("\n********** Processing directory " + directory + " **********\n\n")
    os.chdir(directory)
    for trace_file in glob.glob("trace_assertion_failed_*.c"):
      name = trace_file[:-2]
      trace_index = trace_file[23:-2]
      sys.stdout.write("\n# process " + name + "\n\n")
      proc = subprocess.Popen([vermeer + " -c " + options + " \"" + trace_file + "\" -lm"], stdout=subprocess.PIPE, shell=True)
      proc.wait()
      data_entry_list = []
      while True:
        line = proc.stdout.readline()
        if line != '':
          entries = line.rstrip().split()
          data_entry_list.append(DataEntry(entries[0], entries[2], entries[4], entries[6]))
        else:
          break
      data_set_list.append(DataSet(directory[3:-7], trace_index, data_entry_list))
      subprocess.call(["rm", "-f", "*.o"])
    sys.stdout.write("\n")
    os.chdir(cwd)
  data_file = open("data.txt", "w")
  data_file.write("# Options: " + options + "\n")
  data_file.write("# Benchmark,Trace,")
  for data_entry in data_set_list[0].data_entry_list:
    data_file.write("," + data_entry.category + "-CSs")
    data_file.write("," + data_entry.category + "-Stmts")
    data_file.write("," + data_entry.category + "-Vars")
  data_file.write("\n")
  for data_set in data_set_list:
    data_file.write(data_set.benchmark + "," + data_set.trace_file)
    for data_entry in data_set.data_entry_list:
      data_file.write("," + data_entry.nr_context_switches)
      data_file.write("," + data_entry.nr_statements)
      data_file.write("," + data_entry.nr_variables)
    data_file.write("\n")

