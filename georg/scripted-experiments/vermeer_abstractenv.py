import util.vermeer as vermeer
import sys

if __name__ == "__main__":
  trace_file = sys.argv[1] # e.g., "../traces/bankaccount/locks/trace_assertion_failed_5.c"
  print("Running Vermeer")
  output, time = vermeer.run_vermeer(trace_file, "--keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=abstractenv --flowsensitive --hazardsensitiveall --nointrathreadhazard --smtbeautify")
  print("Runtime: "  + str(time))
  print("Output:")
  for line in output:
    print(line)

