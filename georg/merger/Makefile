.PHONY=all clean merger expr_test graph_test
CXX=g++
CXXFLAGS=-std=c++11 -Wall
MERGER_EXE=merge
MERGER_SRCS=merge_main.cpp merger.cpp error.cpp xml.cpp expr.cpp alphabet.cpp execution2alphabet.cpp program_location.cpp execution.cpp
MERGER_OBJS=$(MERGER_SRCS:%.cpp=%.o)
EXPR_TEST_EXE=exprtest
EXPR_TEST_SRCS=expr_test.cpp error.cpp expr.cpp
EXPR_TEST_OBJS=$(EXPR_TEST_SRCS:%.cpp=%.o)
GRAPH_TEST_EXE=graphtest
GRAPH_TEST_SRCS=graph_test.cpp error.cpp
GRAPH_TEST_OBJS=$(GRAPH_TEST_SRCS:%.cpp=%.o)

IR2C_EXE=ir2c
IR2C_SRCS=ir2c_main.cpp error.cpp xml.cpp execution.cpp expr.cpp
IR2C_OBJS=$(IR2C_SRCS:%.cpp=%.o)

all: merger expr_test graph_test build_ir2c

merger: $(MERGER_OBJS)
	$(CXX) $(CXXFLAGS) -o $(MERGER_EXE) $(MERGER_OBJS)

expr_test: $(EXPR_TEST_OBJS)
	$(CXX) $(CXXFLAGS) -o $(EXPR_TEST_EXE) $(EXPR_TEST_OBJS)

graph_test: $(GRAPH_TEST_OBJS)
	$(CXX) $(CXXFLAGS) -o $(GRAPH_TEST_EXE) $(GRAPH_TEST_OBJS)

build_ir2c: $(IR2C_OBJS)
	$(CXX) $(CXXFLAGS) -o $(IR2C_EXE) $(IR2C_OBJS)

clean:
	rm -f *.o
	rm -f ./$(MERGER_EXE)
	rm -f ./$(EXPR_TEST_EXE)
	rm -f ./$(GRAPH_TEST_EXE)
	rm -f ./$(IR2C_EXE)

