nuwls: basis_pms.h build.h pms.h heuristic.h propagate.h pms.cpp	
	g++  pms.cpp -O3 -o nuwls -static
	rm -f *~
