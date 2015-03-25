import sys
import os
import glob
import subprocess
import time

explanation_file = sys.argv[1]
smt_simplifier = os.environ['VERMEER_PATH'] + "/georg/smt2-simplifier/smtlib_main.native"

sys.stdout.write("Process file " + explanation_file + "\n")

def read_entities_from_file(filename):
  entities = []
  with open(filename, "r") as f:
    entity = None
    for line in f:
      line_stripped = line.strip()
      if line_stripped == "":
        if not entity is None:
          entities.append(entity)
        entity = []
      else:
        entity.append(line_stripped)
    if not entity is None:
      entities.append(entity)
  return entities

def beautify_smt_formula(smt_formula):
  p = subprocess.Popen([smt_simplifier], stdout=subprocess.PIPE, stdin=subprocess.PIPE, stderr=subprocess.STDOUT)
  p_stdout = p.communicate(input=b"" + "(assert " + smt_formula + ")")[0]
  output = p_stdout.decode()
  p.wait()
  result = []
  for line in output.split("\n"):
    rline = line.rstrip()
    if not rline == "":
      result.append(rline)
  return result
  
def process_entities(entities):
  processed_entities = []
  for entity in entities:
    # handle invariant
    smt_formula = entity[0][2:]
    beautified_formula = beautify_smt_formula(smt_formula)
    processed_entity = [ beautified_formula ]
    # is it a TID or a summary?
    if entity[1].startswith("//Tid "):
      # it is a TID
      processed_entity.append("TID")
      processed_entity.append(entity[1][6:])
      for i in range(2, len(entity)):
        processed_entity.append(entity[i])
    else:
      # it is a summary
      processed_entity.append("SUMMARY")
      summary_smt_formula = entity[2][2:]
      beautified_summary_formula = beautify_smt_formula(summary_smt_formula)
      processed_entity.append(beautified_summary_formula)
    processed_entities.append(processed_entity)
  return processed_entities

def print_entities(entities):
  sys.stdout.write("Nr. of entities: " + str(len(entities)) + "\n\n")
  for entity in entities:
    sys.stdout.write("\n")
    formula = entity[0]
    sys.stdout.write("INVARIANT:\n")
    for line in formula:
      sys.stdout.write("  " + line + "\n")
    kind = entity[1]
    if kind == "TID":
      # it is a TID
      sys.stdout.write("STATEMENT (thread " + entity[2] + ", line ")
      if entity[3].startswith("#line "):
        sys.stdout.write(entity[3][6:])
        sys.stdout.write("): \n")
        sys.stdout.write("  " + entity[4] + "\n")
      else:
        sys.stdout.write(entity[4][6:])
        sys.stdout.write("): \n")
        sys.stdout.write("  " + entity[3] + "\n  ")
        sys.stdout.write("  " + entity[5] + "\n")
    else:
      # it is a summary
      sys.stdout.write("SUMMARY: \n")
      for line in entity[2]:
        sys.stdout.write("                    " + line + "\n")

entities = read_entities_from_file(explanation_file)
processed_entities = process_entities(entities)
print_entities(processed_entities)
