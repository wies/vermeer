import sys
import glob
import subprocess
import time
import os
import processes

# runs vermeer on a trace file with a given configuration and returns vermeer's output and runtime
def run_vermeer(trace_file, configuration):
  vermeer = os.environ['VERMEER_PATH'] + "/cil-1.7.3/bin/cilly"
  time_start = time.time() # wall time
  vermeer_exe = vermeer + " -c " + configuration + " \"" + trace_file + "\" -lm"
  proc = subprocess.Popen([ vermeer_exe ], stdout=subprocess.PIPE, stderr=sys.stdout, shell=True)
  proc.wait()
  time_stop = time.time()
  time_delta = time_stop - time_start
  lines = []
  while True:
    line = proc.stdout.readline()
    if line != '':
      lines.append(line.rstrip())
    else:
      break
  subprocess.call(["rm", "-f", "*.o"])
  processes.kill_processes([ "z3 -smt2 -in", "smtinterpol.jar -q" ])
  return lines, time_delta

