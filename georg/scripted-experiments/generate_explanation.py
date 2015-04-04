import sys

from xml.sax.saxutils import escape

def read_file(input_file):
  with open(input_file, "r") as f:
    lines = []
    for line in f:
      lines.append(line.rstrip())
    return lines

def C_to_XML(trace_c, lines_trace_c, out):
  out.write("<cfile src=\"" + trace_c + "\">\n")
  for i in range(0, len(lines_trace_c)):
    line = lines_trace_c[i]
    attrib = ""
    if line.startswith("T_"):
      label = line.split(":")[0]
      parts = label.split("_") # T_1_515_1:
      threadid = parts[1]
      attrib = " threadid=\"" + threadid + "\""
    out.write("<line number=\"" + str(i) + "\"" + attrib + ">\n")
    out.write(escape(lines_trace_c[i]))
    out.write("</line>\n")
  out.write("</cfile>\n")

# generates a fault explanation for the C file trace_c and writes it to the HTML file explanation_html
def generate_explanation(trace_c, explanation_html):
  lines_trace_c = read_file(trace_c)
  C_to_XML(trace_c, lines_trace_c, sys.stdout)

def main():
  if len(sys.argv) <= 2:
    print("Usage: python " + sys.argv[0] + " <trace.c> <explanation.html>")
    return
  generate_explanation(sys.argv[1], sys.argv[2])

if __name__ == "__main__":
  main()

