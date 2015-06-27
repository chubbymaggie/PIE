#include <fstream>
#include <iostream>

#include "cnode/CNode.h"
#include "parser/mistral-parser.h"
#include "Constraint.h"

using namespace std;

string read_file(char *file, bool skip) {
	ifstream myfile(file);
	string t, cur = "";
	if(myfile.is_open()) {
        if(skip) {
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
    string F = read_file(argv[1], argc > 2 && *argv[2] == '0');
    Constraint f(parse_constraint(F, [](const string s) { cout << s << endl; }));

    map<Term*, SatValue> assignment;
    if(f.sat_discard() && f.get_assignment(assignment)) {
        for(auto it = assignment.begin(); it!= assignment.end(); it++) {
            Term* t = it->first;
            SatValue sv = it->second;
            cout << t->to_string() << " : " << sv.to_string() << endl;
        }
    } else cout << "UNSAT" << endl;

    return 0;
}
