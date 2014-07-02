#!/usr/bin/python

#----------------------------------------------------------------------
# Be sure to add the python path that points to the LLDB shared library.
#
# # To use this in the embedded python interpreter using "lldb" just
# import it with the full path using the "command script import"
# command
#   (lldb) command script import /path/to/cmdtemplate.py
#----------------------------------------------------------------------

import commands
import platform
import os
import re
import signal
import sys

try:
    # Just try for LLDB in case PYTHONPATH is already correctly setup
    import lldb
except ImportError:
    lldb_python_dirs = list()
    # lldb is not in the PYTHONPATH, try some defaults for the current platform
    platform_system = platform.system()
    if platform_system == 'Darwin':
        # On Darwin, try the currently selected Xcode directory
        xcode_dir = commands.getoutput("xcode-select --print-path")
        if xcode_dir:
            lldb_python_dirs.append(os.path.realpath(xcode_dir + '/../SharedFrameworks/LLDB.framework/Resources/Python'))
            lldb_python_dirs.append(xcode_dir + '/Library/PrivateFrameworks/LLDB.framework/Resources/Python')
        lldb_python_dirs.append('/System/Library/PrivateFrameworks/LLDB.framework/Resources/Python')
    success = False
    for lldb_python_dir in lldb_python_dirs:
        if os.path.exists(lldb_python_dir):
            if not (sys.path.__contains__(lldb_python_dir)):
                sys.path.append(lldb_python_dir)
                try:
                    import lldb
                except ImportError:
                    pass
                else:
                    print 'imported lldb from: "%s"' % (lldb_python_dir)
                    success = True
                    break
    if not success:
        print "error: couldn't locate the 'lldb' module, please set PYTHONPATH correctly"
        sys.exit(1)


import commands
import optparse
import shlex
import os

def ls(debugger, command, result, internal_dict):
    print >>result, (commands.getoutput('/bin/ls %s' % command))

# And the initialization code to add your commands
def __lldb_init_module(debugger, internal_dict):
    debugger.HandleCommand('command script add -f myscript.ls ls')
    print 'The "ls" python command has been installed and is ready for use.'


def print_process_state (process, thread) :
	if process.GetState() == lldb.eStateStopped:
		print "Stopped, good!"
		stopreason = thread.GetStopReason()
		if stopreason == lldb.eStopReasonBreakpoint:
			print "Breakpoint, good"
		elif stopreason == lldb.eStopReasonException:
			print "eStopReasonException"
			print thread.GetStopDescription(200)
			print error
			#break                    
		elif stopreason == lldb.eStopReasonExec:
			print "eStopReasonExec"
		elif stopreason == lldb.eStopReasonInvalid:
			print "eStopReasonInvalid"
		elif stopreason == lldb.eStopReasonNone:
			print "eStopReasonNone"
		elif stopreason == lldb.eStopReasonPlanComplete:
			print "eStopReasonPlanComplete"
		elif stopreason == lldb.eStopReasonSignal:
			print "eStopReasonSignal"
		elif stopreason == lldb.eStopReasonThreadExiting:
			print "eStopReasonThreadExiting"
		elif stopreason == lldb.eStopReasonTrace:
			print "eStopReasonTrace"
		elif stopreason == lldb.eStopReasonWatchpoint:
			print "eStopReasonWatchpoint"                    
		else:
			print "BAD! %s" % stopreason


def debug_print(exe, args):

    # Create a new debugger instance in your module if your module
    # can be run from the command line. When we run a script from
    # the command line, we won't have any debugger object in
    # lldb.debugger, so we can just create it if it will be needed
    debugger = lldb.SBDebugger.Create()
    
    # When we step or continue, don't return from the function until the process
    # stops. Otherwise we would have to handle the process events ourselves which, while doable is
    #a little tricky.  We do this by setting the async mode to false.
    debugger.SetAsync (False)
    print "Creating a target for '%s'" % exe
    #now create a target:
    target = debugger.CreateTargetWithFileAndArch (exe, lldb.LLDB_ARCH_DEFAULT)
    if target:
        # If the target is valid set a breakpoint at main
        main_bp = target.BreakpointCreateByName ("main", target.GetExecutable().GetFilename());
        print main_bp
    else:
        print "Could not generate breakpoint"

    target_exe = target.GetExecutable()

    # Launch the process. Since we specified synchronous mode, we won't return
    # from this function until we hit the breakpoint at main
    #process = target.LaunchSimple (args, None, os.getcwd())

    launch_info = lldb.SBLaunchInfo(args)
    launch_info.SetWorkingDirectory(os.getcwd())
    error = lldb.SBError()
    process = target.Launch(launch_info, error)    
    #return
     
    # Make sure the launch went ok
    if process:
        # Print some simple process info
        state = process.GetState ()
        print process
        thread = process.GetThreadAtIndex (0)
        

        while True:
            #print_process_state(process, thread)

            frame = thread.GetSelectedFrame()
                        
            if frame:
                #see if we have debug info
                function = frame.GetFunction()
                if function:
					if thread.GetStopReason()==lldb.eStopReasonException:
						print "Exception in %s " % exe
						print error.GetError()
						break
					print function
                else:
                   thread.StepOut()
                   continue


                # Print some simple frame info
                #print frame
                
                # See if we have debug info (a function)
                print "Loc: line {0}, col {1}".format(frame.GetLineEntry().GetLine(), frame.GetLineEntry().GetColumn())
                source_mgr = debugger.GetSourceManager()
                stream = lldb.SBStream()
                source_mgr.DisplaySourceLinesWithLineNumbers(frame.GetLineEntry().GetFileSpec(),
                                                        frame.GetLineEntry().GetLine(),
                                                         0, # context before
                                                         2, # context after
                                                         '=>', # prefix for current line
                                                         stream)
                print stream.GetData()
                
                variables = frame.get_all_variables()
                #print "Vars: %s" % len(variables)
                for variable in variables:
                    print "var: {0} == {1}".format(variable.GetName(), variable.GetValue())
            thread.StepInstruction(0)
            if thread.GetNumFrames()==0: 
                print "Stopped because no stack frame left"
                break


def main():
    if len(sys.argv)<2:
        print "you must give the name of an executable (and optional args)."
        return
    exe = sys.argv[1]
    args = []
    if len(sys.argv)>=2: 
        args = sys.argv[2:]
        #Check if any arg starts with '-', then we have to 
        #'--' to the beginning of the list as required by lldb
        found = False
        for arg in args:
            if arg.startswith('-'):
                #found = True
                break
        if found:
            args.insert(0, "--") 
    debug_print(exe,args)

if __name__ == '__main__':
    main()
elif lldb.debugger:
    # Module is being run inside the LLDB interpreter
    lldb.debugger.HandleCommand('command script add -f ls.ls ls')
    print 'The "ls" python command has been installed and is ready for use.'

