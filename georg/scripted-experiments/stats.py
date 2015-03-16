import os
import sys
import math

class Stats:
  def __init__(self):
    self.stats_cs = dict()
    self.stats_stmts = dict()
    self.stats_vars = dict()
    self.stats_counter = dict()

def collect_stats(datafile_name):
  config_stats = Stats()
  with open(datafile_name, "r") as datafile:
    for line in datafile:
      if not(line.startswith("#")):
        dataitems = line.rstrip().split(",")
        reduction_cs = ((float(dataitems[2])-float(dataitems[5]))/float(dataitems[2]))
        reduction_stmts = ((float(dataitems[3])-float(dataitems[6]))/float(dataitems[3]))
        reduction_vars = ((float(dataitems[4])-float(dataitems[7]))/float(dataitems[4]))
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

for s in str_representation.itervalues():
  print(s + "\\\\")


