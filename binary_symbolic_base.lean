import fixed_program_rows

def iteratePlain (program : BinaryProgram) : Nat → PlainConfig → Option PlainConfig
  | 0, c => some c
  | n+1, c => (plainNext program c).bind (iteratePlain program n)
