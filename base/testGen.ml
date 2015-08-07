open QCheck.Arbitrary

let test_size = 10000

let int_gen = (-3) -- 4
let posInt_gen = 0 -- 6

let intList_gen = list ~len:posInt_gen int_gen
let intListList_gen = list ~len:posInt_gen intList_gen
let intList_int_gen = pair intList_gen int_gen
let int_intList_gen = pair int_gen intList_gen
let intList_intList_gen = pair intList_gen intList_gen
let int_int_List_gen = list ~len:posInt_gen (pair int_gen int_gen)

let intList_tests () = generate ~n:test_size intList_gen
let intListList_tests () = generate ~n:test_size intListList_gen
let intList_int_tests () = generate ~n:test_size intList_int_gen
let int_intList_tests () = generate ~n:test_size int_intList_gen
let intList_intList_tests () = generate ~n:test_size intList_intList_gen
let int_int_List_tests () = generate ~n:test_size int_int_List_gen

let string_gen = string_len (0 -- 12)
let stringList_gen = list ~len:posInt_gen string_gen
let string_int_gen = pair string_gen int_gen
let string_char_gen = pair string_gen char
let string_int_int_gen = triple string_gen int_gen int_gen
let int_char_gen = pair int_gen char
let string_int_char_gen = triple string_gen int_gen char
let string_stringList_gen = pair string_gen stringList_gen

let string_tests () = generate ~n:test_size string_gen
let string_int_tests () = generate ~n:test_size string_int_gen
let string_char_tests () = generate ~n:test_size string_char_gen
let string_int_int_tests () = generate ~n:test_size string_int_int_gen
let int_char_tests () = generate ~n:test_size int_char_gen
let string_int_char_tests () = generate ~n:test_size string_int_char_gen
let string_stringList_tests () = generate ~n:test_size string_stringList_gen

let int_dumper = string_of_int
let char_dumper c = "'" ^ (Char.escaped c) ^ "'"
let string_dumper s = "\"" ^ s ^ "\""
let list_dumper dumper l = "[" ^ (String.concat ", " (List.map dumper l)) ^ "]"
let pair_dumper dumper_1 dumper_2 (a, b) = "(" ^ (dumper_1 a) ^ ", " ^ (dumper_2 b) ^ ")"
let triple_dumper dumper_1 dumper_2 dumper_3 (a, b, c) = "(" ^ (dumper_1 a) ^ ", " ^ (dumper_2 b) ^ ", " ^ (dumper_3 c) ^ ")"

let intList_dumper = list_dumper int_dumper
let intListList_dumper = list_dumper intList_dumper
let intList_int_dumper = pair_dumper intList_dumper int_dumper
let int_intList_dumper = pair_dumper int_dumper intList_dumper
let intList_intList_dumper = pair_dumper intList_dumper intList_dumper
let int_int_List_dumper = list_dumper (pair_dumper int_dumper int_dumper)

let stringList_dumper = list_dumper string_dumper
let string_int_dumper = pair_dumper string_dumper int_dumper
let string_char_dumper = pair_dumper string_dumper char_dumper
let string_int_int_dumper = triple_dumper string_dumper int_dumper int_dumper
let int_char_dumper = pair_dumper int_dumper char_dumper
let string_int_char_dumper = triple_dumper string_dumper int_dumper char_dumper
let string_stringList_dumper = pair_dumper string_dumper stringList_dumper
