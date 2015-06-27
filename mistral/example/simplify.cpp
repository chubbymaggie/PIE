#include <fstream>
#include <iostream>

#include "cnode/CNode.h"
#include "parser/mistral-parser.h"
#include "Constraint.h"

using namespace std;

string read_file(char *file, bool noskip) {
	ifstream myfile(file);
	string t, cur = "";
	if(myfile.is_open()) {
        if(!noskip) {
          std::getline(myfile, t);
          std::getline(myfile, t);
        }
        while(!myfile.eof()) {
            std::getline(myfile, t);
            cur += t + "\n";
        }
    }
	myfile.close();
	return cur;
}

int main(int argc, char **argv) {
    string constraint = read_file(argv[1],  argc > 2 && *argv[2] == '0');
    Constraint c(parse_constraint(constraint, [](const string s) { cout << s << endl; }));
    c.sat();
    cout << c << endl;
    return 0;
}
