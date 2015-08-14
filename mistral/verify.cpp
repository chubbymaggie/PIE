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
    string D = read_file(argv[1], argc > 3 && *argv[3] == '0');
    string F = read_file(argv[2], argc > 4 && *argv[4] == '0');

    Constraint f(parse_constraint(F, [](const string s) { cout << s << endl; }));
    Constraint d(parse_constraint(D, [](const string s) { cout << s << endl; }));

    Constraint query = d & (!f);
    map<Term*, SatValue> assignment;
    if(query.sat_discard() && query.get_assignment(assignment)) {
        for(auto it = assignment.begin(); it!= assignment.end(); it++) {
            Term* t = it->first;
            SatValue sv = it->second;
            cout << t->to_string() << " : " << sv.to_string() << endl;
        }
    } else cout << "UNSAT" << endl;

    return 0;
}
