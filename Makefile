CXX = g++
CXXFLAGS = -std=c++17 -Wall -Wextra -O2

TARGET = main
SRC = main.cpp

$(TARGET): $(SRC)
	$(CXX) $(CXXFLAGS) -o $(TARGET) $(SRC)

clean:
	rm -f $(TARGET)