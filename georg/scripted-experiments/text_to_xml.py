import sys
import os
import glob
import subprocess
import time

from xml.sax.saxutils import escape

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
  
def process_entities(entities):
  processed_entities = []
  for entity in entities:
    # handle invariant
    smt_formula = entity[0][2:]
    processed_entity = [ smt_formula ]
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
      processed_entity.append(summary_smt_formula)
    processed_entities.append(processed_entity)
  return processed_entities

def to_xml(entities, out):
  out.write("<entities>\n")
  for entity in entities:
    out.write("<entity>\n")
    # invariant
    invariant = entity[0] # todo: invariant is currently a list of 
    out.write("<invariant>" + escape(invariant) + "</invariant>\n")
    # what kind of entry is it? (guarded) statement or summary?
    kind = entity[1]
    if kind == "TID":
      # it is a (guarded) statement
      out.write("<kind>STATEMENT</kind>\n")
      # thread id
      threadid = entity[2]
      out.write("<threadid>" + threadid + "</threadid>")
      if entity[3].startswith("#line "):
        line = entity[3]
        guard = ""
        statement = entity[4]
      else:
        line = entity[4]
        guard = entity[3]
        statement = entity[5]
      out.write("<line>" + line[6:] + "</line>\n")
      out.write("<statement>" + escape(statement) + "</statement>\n")
      out.write("<guards>\n")
      if guard != "":
        guard = guard[4:-1] # remove if and outer brackets
        guards = guard.split(" && ")
        for g in guards:
          out.write("<guard>" + escape(g) + "</guard>\n")
      out.write("</guards>\n")
    else:
      # it is a summary
      out.write("<kind>SUMMARY</kind>\n")
      summary = entity[2]
      out.write("<summary>" + escape(summary) + "</summary>\n")
    out.write("</entity>\n")
  out.write("</entities>\n")

if __name__ == "__main__":
  explanation_file = sys.argv[1]
  entities = read_entities_from_file(explanation_file)
  processed_entities = process_entities(entities)
  to_xml(processed_entities, sys.stdout)
