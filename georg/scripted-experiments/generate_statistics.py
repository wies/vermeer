import sys
import os
import glob
import subprocess
import time

class DataEntry:
  def __init__(self, category, nr_context_switches, nr_statements, nr_variables):
    self.category = category
    self.nr_context_switches = nr_context_switches
    self.nr_statements = nr_statements
    self.nr_variables = nr_variables

class DataSet:
  def __init__(self, benchmark, trace_file, data_entry_list, duration):
    self.benchmark = benchmark
    self.trace_file = trace_file
    self.data_entry_list = data_entry_list
    self.duration = duration

cwd = os.getcwd()
vermeer = os.environ['VERMEER_PATH'] + "/cil-1.7.3/bin/cilly"
options = []
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=allthreads --smtcalcstats")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=allthreads --smtcalcstats --flowsensitive --hazardsensitiveall")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=allthreads --smtcalcstats --flowsensitive --hazardsensitiveall --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=allthreads --smtcalcstats --flowsensitive --hazardsensitiveraw --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=allthreads --smtcalcstats --flowsensitive --hazardsensitivewar --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=allthreads --smtcalcstats --flowsensitive --hazardsensitivewaw --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=allthreads --smtcalcstats --flowsensitive --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=allthreads --smtcalcstats --flowsensitive")

options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=partitionTID --smtcalcstats")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=partitionTID --smtcalcstats --flowsensitive --hazardsensitiveall")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=partitionTID --smtcalcstats --flowsensitive --hazardsensitiveall --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=partitionTID --smtcalcstats --flowsensitive --hazardsensitiveraw --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=partitionTID --smtcalcstats --flowsensitive --hazardsensitivewar --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=partitionTID --smtcalcstats --flowsensitive --hazardsensitivewaw --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=partitionTID --smtcalcstats --flowsensitive --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=partitionTID --smtcalcstats --flowsensitive")

options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=partitionGroup --smtcalcstats")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=partitionGroup --smtcalcstats --flowsensitive --hazardsensitiveall")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=partitionGroup --smtcalcstats --flowsensitive --hazardsensitiveall --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=partitionGroup --smtcalcstats --flowsensitive --hazardsensitiveraw --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=partitionGroup --smtcalcstats --flowsensitive --hazardsensitivewar --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=partitionGroup --smtcalcstats --flowsensitive --hazardsensitivewaw --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=partitionGroup --smtcalcstats --flowsensitive --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=partitionGroup --smtcalcstats --flowsensitive")

options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=allgroups --smtcalcstats")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=allgroups --smtcalcstats --flowsensitive --hazardsensitiveall")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=allgroups --smtcalcstats --flowsensitive --hazardsensitiveall --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=allgroups --smtcalcstats --flowsensitive --hazardsensitiveraw --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=allgroups --smtcalcstats --flowsensitive --hazardsensitivewar --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=allgroups --smtcalcstats --flowsensitive --hazardsensitivewaw --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=allgroups --smtcalcstats --flowsensitive --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=allgroups --smtcalcstats --flowsensitive")

options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=abstractenv --smtcalcstats")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=abstractenv --smtcalcstats --flowsensitive --hazardsensitiveall")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=abstractenv --smtcalcstats --flowsensitive --hazardsensitiveall --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=abstractenv --smtcalcstats --flowsensitive --hazardsensitiveraw --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=abstractenv --smtcalcstats --flowsensitive --hazardsensitivewar --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=abstractenv --smtcalcstats --flowsensitive --hazardsensitivewaw --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=abstractenv --smtcalcstats --flowsensitive --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=abstractenv --smtcalcstats --flowsensitive")

options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=nomulti --smtcalcstats")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=nomulti --smtcalcstats --flowsensitive --hazardsensitiveall")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=nomulti --smtcalcstats --flowsensitive --hazardsensitiveall --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=nomulti --smtcalcstats --flowsensitive --hazardsensitiveraw --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=nomulti --smtcalcstats --flowsensitive --hazardsensitivewar --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=nomulti --smtcalcstats --flowsensitive --hazardsensitivewaw --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=nomulti --smtcalcstats --flowsensitive --toposortinput")
options.append("--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=nomulti --smtcalcstats --flowsensitive")

if len(sys.argv) <= 1:
  option_index_range = range(0, len(options))
else:
  try:
    option_index_value = int(sys.argv[1])
    option_index_range = [ option_index_value ]
  except ValueError:
    sys.stdout.write("Usage: " + sys.argv[0] + " <n>\n\nwhere n is an option index in the range [0," + str(len(options) - 1) + "] or is omitted:\n")
    for i in range(0, len(options)):
      sys.stdout.write("Option " + str(i) + ": " + options[i] + "\n")
    sys.stdout.write("\n")
    exit(-1)

for option_index in option_index_range:
  sys.stdout.write("\n########## Processing option \"" + options[option_index] + "\" ##########\n\n")
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
        sys.stdout.flush()
        time_start = time.time() # wall time
        proc = subprocess.Popen([vermeer + " -c " + options[option_index] + " \"" + trace_file + "\" -lm"], stdout=subprocess.PIPE, stderr=sys.stdout, shell=True)
        proc.wait()
        time_stop = time.time()
        data_entry_list = []
        while True:
          line = proc.stdout.readline()
          if line != '':
            entries = line.rstrip().split()
            data_entry_list.append(DataEntry(entries[0], entries[2], entries[4], entries[6]))
          else:
            break
        data_set_list.append(DataSet(directory[3:-7], trace_index, data_entry_list, (time_stop - time_start)))
        subprocess.call(["rm", "-f", "*.o"])
      sys.stdout.write("\n")
      os.chdir(cwd)
    data_file = open("data_option" + str(option_index) + ".dat", "w")
    data_file.write("# Options: " + options[option_index] + "\n")
    data_file.write("# Format: Benchmark,Trace")
    for data_entry in data_set_list[0].data_entry_list:
      data_file.write("," + data_entry.category + "-CSs")
      data_file.write("," + data_entry.category + "-Stmts")
      data_file.write("," + data_entry.category + "-Vars")
    data_file.write(",Time[s]")
    data_file.write("\n")
    for data_set in data_set_list:
      data_file.write(data_set.benchmark + "," + data_set.trace_file)
      for data_entry in data_set.data_entry_list:
        data_file.write("," + data_entry.nr_context_switches)
        data_file.write("," + data_entry.nr_statements)
        data_file.write("," + data_entry.nr_variables)
      data_file.write("," + str(data_set.duration))
      data_file.write("\n")

