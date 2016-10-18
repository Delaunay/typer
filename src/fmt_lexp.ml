
let padding_right (str: string ) (dim: int ) (char_: char) : string =
  let diff = (dim - String.length str)
  in let rpad = max diff 0
  in str ^ (String.make rpad char_)

let padding_left (str: string ) (dim: int ) (char_: char) : string =
  let diff = (dim - String.length str)
  in let lpad = max diff 0
  in (String.make lpad char_) ^ str
