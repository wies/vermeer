all: merger expr_test

merger:
	g++ -std=c++11 -Wall -o merger merger.cpp error.cpp xml.cpp

expr_test:
	g++ -std=c++11 -Wall -o expr_test expr_test.cpp error.cpp

clean:
	rm -f ./merger
	rm -f ./expr_test

