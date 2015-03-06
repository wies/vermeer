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
      proc = subprocess.Popen([vermeer + " -c --keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=allthreads --smtcalcstats --flowsensitive \"" + trace_file + "\" -lm"], stdout=subprocess.PIPE, shell=True)
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
  for data_set in data_set_list:
    print(data_set.benchmark + " & " + data_set.trace_file + " & " + data_set.data_entry_list[0].nr_context_switches + " & " + data_set.data_entry_list[0].nr_statements + " & " + data_set.data_entry_list[0].nr_variables + " & " + data_set.data_entry_list[1].nr_context_switches + " & " + data_set.data_entry_list[1].nr_statements + " & " + data_set.data_entry_list[1].nr_variables + " & " + data_set.data_entry_list[2].nr_context_switches + " & " + data_set.data_entry_list[2].nr_statements + " & " + data_set.data_entry_list[2].nr_variables)
