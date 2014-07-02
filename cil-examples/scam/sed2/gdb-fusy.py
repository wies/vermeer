#!/usr/bin/env python

import gdb

MAXITER = 3


def extract_breakpoint_string( step_string):
	""" receives strings of the form
	Line 6 of "while.c" starts at address 0x100000f71 <main+18> and ends at 0x100000f73 <main+20>. 
	and turns them into breakpoint locations of the form
	while.c:6
	"""
	tokens = step_string.split( );
	assert tokens[0]=="Line"
	""" add an offset of 1 to the line to make 
		sure that we are inside the loop. 
		This is a hack!
	"""
	line_number = int(tokens[1])+1
	assert tokens[2]=="of"
	file_name = tokens[3].replace('"', '').strip()	
	return "{0}:{1}".format(file_name,line_number) 

def find_loops():
	found_loops = set()

	gdb.execute("break main", False, True)
	gdb.execute("run", False, True)

	while True:
		try:
			step_info = gdb.execute("step", False, True)
		except Exception as err:
			""" delete the breakpoint in 'main' """
			gdb.execute("clear main", False, True)
			return found_loops 
		for line in step_info.split('\n'):
			if ("while" in line) or ("for" in line):
				found_loops.add(extract_breakpoint_string(gdb.execute("info line", False, True)))
	
def create_breakpoints( bplist):
	bp_map = dict()
	for bplabel in bplist:
		bp_string = gdb.execute("break %s"%bplabel, False, True)
		tokens = bp_string.split( );
		assert tokens[0]=="Breakpoint"
		bp_id = int(tokens[1])
		bp_map[bp_id] = bplabel
	return bp_map

def delete_breakpoints( bpmap):
	for key in bpmap:
		result = gdb.execute("clear %s"%bpmap[key], False, True)


def get_breakpoint_id( info):
	for line in info.split('\n'):
		tokens = line.split( );
		if len(tokens)<2: continue
		if tokens[0]=="Breakpoint":
			return int(tokens[1].replace(',','').strip() )
	return -1
	
def show_current_variables():
	locals_string = gdb.execute("info locals", False, True)
	globals_string = gdb.execute("info variables", False, True)
	args_string = gdb.execute("info args", False, True)
	print "locals %s\n" % locals_string
	print "globals %s\n" % globals_string
	print "args %s\n" % args_string

def dynamic_fusy( bpmap): 
	info = gdb.execute("run", False, True)
	while True:
		try:
			bp_id = get_breakpoint_id(info)
			if bp_id<0:
				print "No more breakpoints. Done"
				return			
			bp_info = gdb.execute("info break %s"%bp_id, False, True).split('\n')
			for line in bp_info:
				if "breakpoint already hit" in line:
					tokens = line.split( );
					hitcount = int(tokens[3])
					print "Hit Count: %s" % hitcount
					if hitcount >= MAXITER:		
						gdb.execute("disable %s" % bp_id, False, True)	
			show_current_variables()
			info = gdb.execute("continue", False, True)	
		except Exception as err:
			print "Execution stopped:\n%s"%err
			return



""" turn pagination off """
gdb.execute("set height unlimited", False, True)
gdb.execute("set width unlimited", False, True)

""" find all lines that contain a loop """        
loop_lines = find_loops()

""" create a breakpoints at these lines  """
bpmap = create_breakpoints(loop_lines)

gdb.execute("info breakpoints")

""" collect the values of all variables in the first MAXITER iterations"""
dynamic_fusy(bpmap)

""" remove all create breakpoints  """
delete_breakpoints(bpmap)


