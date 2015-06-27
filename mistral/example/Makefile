all: abduce chkSAT chkVALID simplify verify

abduce: abduce.cpp
	g++ -I.. -I../cnode -I../solver -I../numeric-lib -I../term/ -std=c++11 abduce.cpp ../build/parser/libparser.a ../build/libmistral.a -lgmp -o abduce

chkSAT: chkSAT.cpp
	g++ -I.. -I../cnode -I../solver -I../numeric-lib -I../term/ -std=c++11 chkSAT.cpp ../build/parser/libparser.a ../build/libmistral.a -lgmp -o chkSAT

chkVALID: chkVALID.cpp
	g++ -I.. -I../cnode -I../solver -I../numeric-lib -I../term/ -std=c++11 chkVALID.cpp ../build/parser/libparser.a ../build/libmistral.a -lgmp -o chkVALID

simplify: simplify.cpp
	g++ -I.. -I../cnode -I../solver -I../numeric-lib -I../term/ -std=c++11 simplify.cpp ../build/parser/libparser.a ../build/libmistral.a -lgmp -o simplify

verify: verify.cpp
	g++ -I.. -I../cnode -I../solver -I../numeric-lib -I../term/ -std=c++11 verify.cpp ../build/parser/libparser.a ../build/libmistral.a -lgmp -o verify

clean:
	rm -rf abduce chkSAT chkVALID simplify verify
