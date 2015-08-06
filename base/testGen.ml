open QCheck.Arbitrary

let test_size = 8192

let int_gen = (-3) -- 4
let posInt_gen = 0 -- 6

let intList_gen = list ~len:posInt_gen int_gen
let intListList_gen = list ~len:posInt_gen intList_gen
let intList_int_gen = pair intList_gen int_gen
let int_intList_gen = pair int_gen intList_gen
let intList_intList_gen = pair intList_gen intList_gen
let int_int_List_gen = list ~len:posInt_gen (pair int_gen int_gen)

let intList_tests = generate ~n:test_size intList_gen
let intListList_tests = generate ~n:test_size intListList_gen
let intList_int_tests = generate ~n:test_size intList_int_gen
let int_intList_tests = generate ~n:test_size int_intList_gen
let intList_intList_tests = generate ~n:test_size intList_intList_gen
let int_int_List_tests = generate ~n:test_size int_int_List_gen

let string_gen = string_len (0 -- 12)
let string_int_gen = pair string_gen int_gen
let string_char_gen = pair string_gen char
let string_int_int_gen = triple string_gen int_gen int_gen
let int_char_gen = pair int_gen char
let string_int_char_gen = triple string_gen int_gen char

let string_tests = generate ~n:test_size string_gen
let string_int_tests = generate ~n:test_size string_int_gen
let string_char_tests = generate ~n:test_size string_char_gen
let string_int_int_tests = generate ~n:test_size string_int_int_gen
let int_char_tests = generate ~n:test_size int_char_gen
let string_int_char_tests = generate ~n:test_size string_int_char_gen
