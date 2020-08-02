# Lambda calculus evaluator
A (probably incorrect) stab at a lambda calculus evaluator for LinqPad in F#

It uses f# match expressions to parse the input

The parsed AST then has all local vars converted to deBruijn indices
The result is then reduced to its simplest form
