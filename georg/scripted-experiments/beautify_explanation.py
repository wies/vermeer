import sys
import os
import glob
import subprocess
import time

explanation_file = sys.argv[1]
smt_simplifier = os.environ['VERMEER_PATH'] + "/georg/smt2-simplifier/smtlib_main.native"

with open(explanation_file, "r") as f:
  next = False
  for line in f:
    line_stripped = line.strip()
    if line_stripped == "":
      sys.stdout.write(line)
      next = True
    else:
      if next:
        next = False
        smt_formula = line_stripped[2:]
        p = subprocess.Popen([smt_simplifier], stdout=subprocess.PIPE, stdin=subprocess.PIPE, stderr=subprocess.STDOUT)
        p_stdout = p.communicate(input=b"" + "(assert " + smt_formula + ")")[0]
        sys.stdout.write(line)
        print("/*")
        sys.stdout.write(p_stdout.decode())
        print("*/")
        p.wait()
      else:
        sys.stdout.write(line)
