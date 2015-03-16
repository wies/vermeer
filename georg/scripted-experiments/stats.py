import os
import sys
import math

class Stats:
  def __init__(self):
    self.stats_cs = dict()
    self.stats_stmts = dict()
    self.stats_vars = dict()
    self.stats_counter = dict()

def read_dataset(datafile_name):
  dataset = dict()
  with open(datafile_name, "r") as datafile:
    for line in datafile:
      if not(line.startswith("#")):
        dataitems = line.rstrip().split(",")
        key = dataitems[0]
        if key in dataset:
          dataset[key].append(dataitems)
        else:
          dataset[key] = [ dataitems ]

def reduction(old, new):
  return ((float(old)-float(new))/float(old))

def collect_stats(datafile_name):
  config_stats = Stats()
  with open(datafile_name, "r") as datafile:
    for line in datafile:
      if not(line.startswith("#")):
        dataitems = line.rstrip().split(",")
        reduction_cs = reduction(dataitems[2], dataitems[5])
        reduction_stmts = reduction(dataitems[3], dataitems[6])
        reduction_vars = reduction(dataitems[4], dataitems[7])
        key = dataitems[0]
        if key in config_stats.stats_cs:
          config_stats.stats_cs[key] += reduction_cs
          config_stats.stats_stmts[key] += reduction_stmts
          config_stats.stats_vars[key] += reduction_vars
          config_stats.stats_counter[key] += 1
        else:
          config_stats.stats_cs[key] = reduction_cs
          config_stats.stats_stmts[key] = reduction_stmts
          config_stats.stats_vars[key] = reduction_vars
          config_stats.stats_counter[key] = 1
  return config_stats

stats = []
for i in range(1, len(sys.argv)):
  stats.append(collect_stats(sys.argv[i]))

config_stats = stats[0]
str_representation = dict()
for s in config_stats.stats_cs.iteritems():
  str_representation[s[0]] = (s[0] + " & " + str(config_stats.stats_counter[s[0]]))

for config_stats in stats:
  for s in config_stats.stats_cs.iteritems():
    red_cs_perc = int(math.floor(0.5 + 100*(s[1]/config_stats.stats_counter[s[0]])))
    red_stmts_perc = int(math.floor(0.5 + 100*(config_stats.stats_stmts[s[0]]/config_stats.stats_counter[s[0]])))
    red_vars_perc = int(math.floor(0.5 + 100*(config_stats.stats_vars[s[0]]/config_stats.stats_counter[s[0]])))
    str_representation[s[0]] += " & " + str(red_cs_perc) + " & " + str(red_stmts_perc) + " & " + str(red_vars_perc)

keys = list(str_representation.keys())
keys.sort()
for key in keys:
  s = str_representation[key]
  print(s + "\\\\")


