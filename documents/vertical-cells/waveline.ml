let offset = 5;

let one_wave x y =
  [ string_of_int x; string_of_int y; "moveto";
    string_of_int (x + offset); string_of_int (y + offset);
    string_of_int (x + offset); string_of_int (y + 2 * offset);
    string_of_int x; string_of_int (y + 3 * offset); "curveto";
    string_of_int (x - offset); string_of_int (y + 4 * offset);
    string_of_int (x - offset); string_of_int (y + 5 * offset);
    string_of_int x; string_of_int (y + 6 * offset); "curveto"]
    

let rec vertical_waveline x1 y1 length =
  if length < 30 then
  [ string_of_int x1; string_of_int y1; "moveto";
    string_of_int x1; string of_int (y1 + length); "lineto" ]
  else
    one_wave x1 y1 @ vertical_waveline x1 (y1 + 30) (length - 30)