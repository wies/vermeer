import sys
import os

comments = []
faulty_entries = []
entries = []
index = sys.argv[1]

if len(sys.argv) <= 1:
  sys.stdout.write("Usage: " + sys.argv[0] + " <n>\nwhere n is an option index\n")
  exit(-1)
else:
  try:
    option_index_value = int(sys.argv[1])
  except ValueError:
    sys.stdout.write("Usage: " + sys.argv[0] + " <n>\nwhere n is an option index\n")
    exit(-1)

datadirectory = "./data/config-" + str(option_index_value)

with open(datadirectory + "/data_option" + str(option_index_value) + ".dat", "r") as f:
  for line in f:
    line_stripped = line.strip()
    if line_stripped.startswith("#"):
      comments.append(line)
    else:
      if len(line_stripped.split(",")) != 27:
        faulty_entries.append(line)
      else:
        entries.append(line)

with open(datadirectory + "/data_option" + str(option_index_value) + ".filtered.dat", "w") as pos_f:
  for line in comments:
    pos_f.write(line)
  for line in entries:
    pos_f.write(line)

with open(datadirectory + "/data_option" + str(option_index_value) + ".faulty.dat", "w") as neg_f:
  for line in comments:
    neg_f.write(line)
  for line in faulty_entries:
    neg_f.write(line)

