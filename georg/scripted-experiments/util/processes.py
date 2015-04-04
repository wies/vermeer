import os
import subprocess
import sys
import signal

# kills processes that end with strings given in process_descriptions
def kill_processes(process_descriptions):
  ps_proc = subprocess.Popen(["ps -aux | grep $USER"], stdout=subprocess.PIPE, stderr=sys.stdout, shell=True)
  ps_proc.wait()
  while True:
    line = ps_proc.stdout.readline().rstrip()
    if line != '':
      if (len(filter(lambda x: line.endswith(x), process_descriptions)) > 0):
        # kill this process
        proc_infos = line.split()
        os.kill(int(proc_infos[1]), signal.SIGKILL)
    else:
      break

