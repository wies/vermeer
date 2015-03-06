import sys
import os
import glob
import subprocess

cwd = os.getcwd()
vermeer = os.environ['VERMEER_PATH'] + "/cil-1.7.3/bin/cilly"

with open("directories.txt", "r") as f:
  for line in f:
    directory = line.strip()
    sys.stdout.write("\n********** Processing directory " + directory + " **********\n\n")
    os.chdir(directory)
    for trace_file in glob.glob("trace_assertion_failed_*.c"):
      name = trace_file[:-2]
      sys.stdout.write("\n# process " + name + "\n\n")
      proc = subprocess.Popen([vermeer + " -c --keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=allthreads --smtcalcstats --flowsensitive \"" + trace_file + "\" -lm"], stdout=subprocess.PIPE, shell=True)
      proc.wait()
      while True:
        line = proc.stdout.readline()
        if line != '':
          entries = line.rstrip().split()
          print(entries)
        else:
          break
      subprocess.call(["rm", "-f", "*.o"])
    sys.stdout.write("\n")
    os.chdir(cwd)
