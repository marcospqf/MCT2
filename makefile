main: build/main.o build/MCTS.o
	g++ -std=c++14 -O2 -Wall build/main.o build/MCTS.o -o exe
build/main.o: source/main.cpp 
	g++ -std=c++14 -O2 -Wall -g -c source/main.cpp -o build/main.o
build/MCTS.o:	source/MCTS.cpp source/MCTS.hpp
	g++ -std=c++14 -O2 -Wall -g -c source/MCTS.cpp -o build/MCTS.o
clean:
	rm ./build/*.o
