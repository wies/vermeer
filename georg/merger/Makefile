.PHONY=all clean merger expr_test graph_test
CXX=g++
CXXFLAGS=-std=c++11 -Wall
MERGER_EXE=merge
EXPR_TEST_EXE=exprtest
GRAPH_TEST_EXE=graphtest

all: merger expr_test graph_test

merger:
	$(CXX) $(CXXFLAGS) -o $(MERGER_EXE) merger.cpp error.cpp xml.cpp expr.cpp

expr_test:
	$(CXX) $(CXXFLAGS) -o $(EXPR_TEST_EXE) expr_test.cpp error.cpp expr.cpp

graph_test:
	$(CXX) $(CXXFLAGS) -o $(GRAPH_TEST_EXE) graph_test.cpp error.cpp

clean:
	rm -f ./$(MERGER_EXE)
	rm -f ./$(EXPR_TEST_EXE)
	rm -f ./$(GRAPH_TEST_EXE)

