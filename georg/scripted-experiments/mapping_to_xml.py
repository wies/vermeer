import sys
import os
import glob
import subprocess
import time

trace_file = sys.argv[1]

def read_entities_from_file(filename):
  entities = []
  with open(filename, "r") as f:
    for line in f:
      line_stripped = line.strip();
      # local variables format: 
      # int x_29_0;//main::m T0
      # global variables format:
      # int x_0_0;//global::nr_of_pushes
      if line_stripped.startswith("int x_"):
        big_parts = line_stripped.split("//")
        assert(len(big_parts) == 2)
        # extract SSA variable
        ssa_variable = big_parts[0].split(" ")[1][:-1]
        # extract program variable
        small_parts = big_parts[1].split(" ")
        program_variable = small_parts[0]
        if len(small_parts) == 2:
          # local variable with thread id
          threadid = small_parts[1]
        else:
          threadid = None
        entities.append((ssa_variable, program_variable, threadid))
  return entities

def to_xml(entities, out):
  out.write("<variablemappings>\n")
  for entity in entities:
    out.write("<variablemapping>\n")
    out.write("<ssavariable>\n")
    out.write("<string>" + entity[0] + "</string>\n")
    out.write("<index>" + entity[0].split("_")[2] + "</index>\n")
    out.write("</ssavariable>\n")
    out.write("<programvariable>" + entity[1] + "</programvariable>\n")
    if not entity[2] is None:
      out.write("<threadid>" + entity[2] + "</threadid>\n")
    out.write("</variablemapping>\n")
  out.write("</variablemappings>\n")

entities = read_entities_from_file(trace_file)
to_xml(entities, sys.stdout)
