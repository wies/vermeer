import sys
import os
import subprocess

import xml.etree.ElementTree as etree

def beautify_smt_formula(smt_formula):
  smt_simplifier = os.environ['VERMEER_PATH'] + "/cil-1.7.3/bin/smt_simplify"
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

def smt_to_text(smt_formula):
  return smt_formula
  parts = beautify_smt_formula(smt_formula)
  result = ""
  for part in parts:
    result += part + "<br/>\n"
  return result

def write_header(out, title):
  out.write("<head>\n")
  out.write("<title>" + title + "</title>\n")
  out.write("<style>.if { font-weight: bold; }</style>\n")
  out.write("<style>table { border-spacing: 0px; }</style>\n")
  out.write("<style>table td { vertical-align: top; }</style>\n")
  out.write("<style>table td.invariant { padding-right: 0.5cm; }</style>\n")
  out.write("<style>table td.summary { border-left: dashed 2px black; padding-left: 0.5cm; }</style>\n")
  out.write("<style>table td.fillersummary { border-top: dashed 2px black; border-bottom: dashed 2px black; }</style>\n")
  out.write("<style>table td.fillerstmt { border-left: dashed 2px black; background-color: #F9F9F9; }</style>\n")
  out.write("<style>table td.fillerline { background-color: #F9F9F9; }</style>\n")
  out.write("<style>table td.stmt { border-left: dashed 2px black; padding-left: 0.5cm; background-color: #eee; white-space: nowrap; }</style>\n")
  out.write("<style>table td.errorstmt { font-weight: bold; color: #FFFFFF; border-left: dashed 2px black; padding-left: 0.5cm; background-color: #ff0000; white-space: nowrap; }</style>\n")
  out.write("<style>table td.line { background-color: #eee; white-space: nowrap; }</style>\n")
  out.write("<style>table td.errorline { color: #FFFFFF; background-color: #ff0000; white-space: nowrap; }</style>\n")
  out.write("<script src='https://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS-MML_HTMLorMML'></script>\n")
  out.write("<script type=\"text/x-mathjax-config\">")
  out.write("MathJax.Hub.Config({tex2jax: {inlineMath: [['$','$'], ['\\\\(','\\\\)']]}});")
  out.write("</script>\n")
  out.write("</head>\n")

def write_invariant(traceelement, out):
  out.write("<tr>\n")
  out.write("<td align=\"right\" class=\"invariant\">" + smt_to_text(traceelement.find("invariant").text) + "</td><td class=\"fillerstmt\">&nbsp;</td><td class=\"fillerline\"/><td/>\n")
  out.write("</tr>\n")

def write_statement(traceelement, out):
  guards = []
  for guard in traceelement.iter("guard"):
    guards.append(guard.text)
  if traceelement.find("statement").text.startswith("assert("):
    stmtclass = "errorstmt"
    lineclass = "errorline"
  else:
    stmtclass = "stmt"
    lineclass = "line"
  if len(guards) > 0:
    guard_string = ""
    first_guard = True
    for guard in guards:
      if not first_guard:
        guard_string += " AND "
      else:
        first_guard = False
      guard_string += smt_to_text(guard)
    out.write("<tr><td/><td class=\"" + stmtclass + "\"><span class=\"if\">if</span> (" + guard_string + ")</td><td class=\"" + lineclass + "\">(thread " + traceelement.attrib["threadid"] + ", line " + traceelement.attrib["line"] + ") </td></tr>\n")
    out.write("<tr><td/><td class=\"" + stmtclass + "\">&nbsp;&nbsp;&nbsp;&nbsp;" + traceelement.find("statement").text + "</td><td class=\"" + lineclass + "\"/></tr>\n")
  else:
    out.write("<tr><td/><td class=\"" + stmtclass + "\">" + traceelement.find("statement").text + "</td><td class=\"" + lineclass + "\">(thread " + traceelement.attrib["threadid"] + ", line " + traceelement.attrib["line"] + ")</td></tr>\n")
    # TODO add special handling for assertion

def write_summary(traceelement, out):
  out.write("<tr>\n")
  out.write("<td/><td class=\"fillersummary\">&nbsp;</td><td class=\"fillersummary\">&nbsp;</td><td class=\"summary\">" + smt_to_text(traceelement.find("summary").text) + "</td>\n")
  out.write("</tr>\n")

def write_html_file(xml_explanation, out):
  out.write("<html>\n")
  # write header
  title = explanation.attrib["trace_c"] + " --- " + explanation.attrib["explanation"]
  write_header(out, title)

  # write body
  out.write("<body>\n")
  out.write("<table>\n")
  out.write("<tr><th>Invariant</th><th colspan=\"2\">Statement</th><th>Summary</th></tr>\n")
  for traceelement in xml_explanation.iter("traceelement"):
    # write invariant
    write_invariant(traceelement, out)
    # write content
    if traceelement.attrib["kind"] == "STATEMENT":
      write_statement(traceelement, out)
    else:
      write_summary(traceelement, out)
  out.write("</table>\n")
  out.write("</body>\n")
  out.write("</html>\n")

if __name__ == "__main__":
  xml_file = sys.argv[1]
  tree = etree.parse(xml_file)
  root = tree.getroot()
  for explanation in root.iter("explanation"):
    write_html_file(explanation, sys.stdout)  

#  print(etree.tostring(root, 'utf-8'))

