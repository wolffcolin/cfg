CXX = g++
CXXFLAGS = -std=c++17 -Wall -Wextra -Wpedantic -Wshadow -Wconversion -Wsign-conversion \
           -Wnull-dereference -Wdouble-promotion -Wformat=2 -Wold-style-cast \
           -Wcast-align -Wcast-qual -Wnon-virtual-dtor -Woverloaded-virtual \
           -Wzero-as-null-pointer-constant -g3 -fno-omit-frame-pointer \
           -fno-optimize-sibling-calls -Wlogical-op -Wduplicated-cond -Wduplicated-branches -O2
TARGET = main
SRC = main.cpp

$(TARGET): $(SRC)
	$(CXX) $(CXXFLAGS) -o $(TARGET) $(SRC)

clean:
	rm -f $(TARGET)