let offset = 5;;

let one_wave x y =
  [ string_of_int (x + offset); string_of_int (y + offset);
    string_of_int (x + offset); string_of_int (y + 2 * offset);
    string_of_int x; string_of_int (y + 3 * offset); "curveto";
    string_of_int (x - offset); string_of_int (y + 4 * offset);
    string_of_int (x - offset); string_of_int (y + 5 * offset);
    string_of_int x; string_of_int (y + 6 * offset); "curveto\n"];;
    

let rec vertical_waveline_aux x1 y1 length =
  if length < 6 * offset then
  [ string_of_int x1; string_of_int (y1 + length); "lineto\n" ]
  else
    one_wave x1 y1 @ vertical_waveline_aux x1 (y1 + 30) (length - 30);;

let vertical_wave_line x1 y1 length =
  print_string (String.concat " " ("" :: vertical_waveline_aux x1 y1 length));;