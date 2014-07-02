import sys
from subprocess import Popen, PIPE
from shlex import split



def main():
	print "Started from command line. good!"

	if len(sys.argv)<2:
		print "you must give the name of an executable (and optional args)."
		return
	exe = sys.argv[1]
	args = []
	if len(sys.argv)>=2: 
		args = sys.argv[2:]
	
	gdb_command = "gdb --args {0} {1} ".format(exe,' '.join(args))

	p1 = Popen(split("echo source gdb-fusy.py"), stdout=PIPE)
	p2 = Popen(split(gdb_command), stdin=p1.stdout)
	p2.wait()

if __name__ == '__main__':
    main()


