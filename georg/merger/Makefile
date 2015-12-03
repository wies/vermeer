CXX=g++
CXXFLAGS=-std=c++11 -Wall

all: merger expr_test

merger:
	$(CXX) $(CXXFLAGS) -o merger merger.cpp error.cpp xml.cpp

expr_test:
	$(CXX) $(CXXFLAGS) -o expr_test expr_test.cpp error.cpp

clean:
	rm -f ./merger
	rm -f ./expr_test

