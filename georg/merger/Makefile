.PHONY=all clean merger expr_test
CXX=g++
CXXFLAGS=-std=c++11 -Wall
MERGER_EXE=merge
EXPR_TEST_EXE=exprtest

all: merger expr_test

merger:
	$(CXX) $(CXXFLAGS) -o $(MERGER_EXE) merger.cpp error.cpp xml.cpp

expr_test:
	$(CXX) $(CXXFLAGS) -o $(EXPR_TEST_EXE) expr_test.cpp error.cpp

clean:
	rm -f ./$(MERGER_EXE)
	rm -f ./$(EXPR_TEST_EXE)

