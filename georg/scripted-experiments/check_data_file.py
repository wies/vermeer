import sys
import os

comments = []
faulty_entries = []
entries = []

with open("data_option1.dat", "r") as f:
  for line in f:
    line_stripped = line.strip()
    if line_stripped.startswith("#"):
      comments.append(line)
    else:
      if len(line_stripped.split(",")) != 27:
        faulty_entries.append(line)
      else:
        entries.append(line)

with open("data_option1.filtered.dat", "w") as pos_f:
  for line in comments:
    pos_f.write(line)
  for line in entries:
    pos_f.write(line)

with open("data_option1.faulty.dat", "w") as neg_f:
  for line in comments:
    neg_f.write(line)
  for line in faulty_entries:
    neg_f.write(line)

