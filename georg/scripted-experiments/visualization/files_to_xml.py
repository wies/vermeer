import sys

import text_to_xml
import mapping_to_xml

if __name__ == "__main__":
  explanation_file = sys.argv[1]
  trace_file = sys.argv[2]

  explanation_entities = text_to_xml.read_entities_from_file(explanation_file)
  processed_explanation_entities = text_to_xml.process_entities(explanation_entities)

  mapping_entities = mapping_to_xml.read_entities_from_file(trace_file)

  sys.stdout.write("<?xml version=\"1.0\"?>\n")
  sys.stdout.write("<explanation>\n")
  text_to_xml.to_xml(processed_explanation_entities, sys.stdout)
  mapping_to_xml.to_xml(mapping_entities, sys.stdout)
  sys.stdout.write("</explanation>\n")


