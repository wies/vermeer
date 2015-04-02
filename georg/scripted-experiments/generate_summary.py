import subprocess
import sys
import os
import signal

def process_trace(trace_file, configuration):
  vermeer = os.environ['VERMEER_PATH'] + "/cil-1.7.3/bin/cilly"
  name = trace_file[:-2]
  trace_index = trace_file[23:-2]
  sys.stdout.write("\n# process " + name + "\n\n")
  sys.stdout.flush()
  proc = subprocess.Popen([vermeer + " -c " + configuration + " \"" + trace_file + "\" -lm"], stdout=subprocess.PIPE, stderr=sys.stdout, shell=True)
  proc.wait()
  while True:
    line = proc.stdout.readline()
    if line != '':
      sys.stdout.write(line)
    else:
      break
  subprocess.call(["rm", "-f", "*.o"])
  cleanup_processes()

def cleanup_processes():
  ps_proc = subprocess.Popen(["ps -aux | grep $USER"], stdout=subprocess.PIPE, stderr=sys.stdout, shell=True)
  ps_proc.wait()
  while True:
    line = ps_proc.stdout.readline().rstrip()
    if line != '':
      if (line.endswith("z3 -smt2 -in") or line.endswith("smtinterpol.jar -q")):
        proc_infos = line.split()
        os.kill(int(proc_infos[1]), signal.SIGKILL)
    else:
      break

if __name__ == "__main__":
  option = "--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=abstractenv --flowsensitive --hazardsensitiveall --toposortinput --nointrathreadhazard"
  #process_trace("../traces/pool/locks/trace_assertion_failed_137.c", option)
  process_trace("../traces/bankaccount/locks/trace_assertion_failed_5.c", option)
