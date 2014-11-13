rm -f *.linear.c \
      *.postlinear.c \
      *.postlinear.broken.c \
      *.concrete.c \
      *.postconcrete.c \
      *.postconcrete.notmps.c \
      *.ssa.c \
      *.cil.c \
      *.i \
      *.o \
      *~ \
      smt/single_solver.smt2 \
      a.out

if [ -d smt ]; then rmdir smt; fi
