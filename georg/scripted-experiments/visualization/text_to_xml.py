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
  out.write("<trace>\n")
  for entity in entities:
    attribute_string = ""
    #out.write("<traceelement>\n")
    # invariant
    invariant = entity[0] # todo: invariant is currently a list of 
    content_string = "<invariant>" + escape(invariant) + "</invariant>\n"
    #out.write("<invariant>" + escape(invariant) + "</invariant>\n")
    # what kind of entry is it? (guarded) statement or summary?
    kind = entity[1]
    if kind == "TID":
      # it is a (guarded) statement
      attribute_string += " kind=\"STATEMENT\""
      #out.write("<kind>STATEMENT</kind>\n")
      # thread id
      threadid = entity[2]
      attribute_string += " threadid=\"" + threadid + "\""
      #out.write("<threadid>" + threadid + "</threadid>")
      if entity[3].startswith("#line "):
        line = entity[3]
        guard = ""
        statement = entity[4]
      else:
        line = entity[4]
        guard = entity[3]
        statement = entity[5]
      attribute_string += " line=\"" + line[6:] + "\""
      #out.write("<line>" + line[6:] + "</line>\n")
      content_string += "<statement>" + escape(statement) + "</statement>\n"
      #out.write("<statement>" + escape(statement) + "</statement>\n")
      content_string += "<guards>\n"
      #out.write("<guards>\n")
      if guard != "":
        guard = guard[4:-1] # remove if and outer brackets
        guards = guard.split(" && ")
        for g in guards:
          content_string += "<guard>" + escape(g) + "</guard>\n"
          #out.write("<guard>" + escape(g) + "</guard>\n")
      content_string += "</guards>\n"
      #out.write("</guards>\n")
    else:
      # it is a summary
      attribute_string += " kind=\"SUMMARY\""
      #out.write("<kind>SUMMARY</kind>\n")
      summary = entity[2]
      content_string += "<summary>" + escape(summary) + "</summary>\n"
      #out.write("<summary>" + escape(summary) + "</summary>\n")
    out.write("<traceelement" + attribute_string + ">\n")
    out.write(content_string)
    out.write("</traceelement>\n")
  out.write("</trace>\n")

if __name__ == "__main__":
  explanation_file = sys.argv[1]
  entities = read_entities_from_file(explanation_file)
  processed_entities = process_entities(entities)
  to_xml(processed_entities, sys.stdout)
