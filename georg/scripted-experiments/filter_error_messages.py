import sys
import os

dat_file = sys.argv[1]
out_file = sys.argv[2]

with open(dat_file, "r") as f_dat:
  for line in f_dat:
    line_stripped = line.strip()
    if not line_stripped.startswith("#"):
      entries = line_stripped.split(",")
      benchmark = entries[0]
      trace_index = entries[1]
      with open(out_file, "r") as f_out:
        start_matching = False
        start_printing = False
        for line_out in f_out:
          if start_matching:
            if line_out.startswith("********** Processing directory ../"):
              start_matching = False
            else:
              if start_printing:
                if line_out.startswith("# process trace_assertion_failed_"):
                  start_printing = False
                else:
                  sys.stdout.write(line_out)
              else:
                if line_out.strip() == "# process trace_assertion_failed_" + trace_index:
                  start_printing = True
                  sys.stdout.write(benchmark + "\n")
                  sys.stdout.write(line_out)
          else:
            if line_out.startswith("********** Processing directory ../traces/" + benchmark + "/locks **********"):
              start_matching = True
            else:
              if line_out.startswith("********** Processing directory ../"):
                start_matching = False
