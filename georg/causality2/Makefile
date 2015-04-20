all:
	g++ -std=c++11 -Wall -o causality main.cpp cbmc.cpp causality.cpp -lpthread

test_cbmc:
	g++ -std=c++11 -Wall -o TestCBMC test_cbmc.cpp cbmc.cpp -lpthread

test_cbmc2:
	g++ -std=c++11 -Wall -o TestCBMC2 test_cbmc2.cpp cbmc.cpp -lpthread

test_cbmc3:
	g++ -std=c++11 -Wall -o TestCBMC3 test_cbmc3.cpp cbmc.cpp -lpthread

test_cbmc4:
	g++ -std=c++11 -Wall -o TestCBMC4 test_cbmc4.cpp cbmc.cpp -lpthread

clean:
	rm -f ./SyMPC
	rm -f ./TestCBMC*
	rm -f *.o
	rm -f *~
	rm -f *.out

