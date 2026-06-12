CORE: datastructures for terms, literals, clauses, substitutions, unification, indexing, etc.

We mostly follow vampire.

Terms are internalized in a bank. Term constructors are memoised by name and arity. 
Literals are integers (opaque type Literal = Int)
literals are also terms with a polarity (predicates are represented exactly as functions). The term bank is used to refer to the head of a term, its children, its free variables, etc.
some controll bits in the terms say if it is a compound term or a variable. If it's compound, the children are stored in an array. 

Free variables are stored via a mask that is exact for the first 63 variables, so that the free variable of a compound term is the OR of its children. This allows to quickly check if a term contains a free variable, and which one it is. Also if it is ground. If there are more than 63 variables (first bit on), we need to do full traversal instead.

We run efficient unification that does not eagerly substitute. This means dereferencing (when variables are mapped to other variables) like it is done in Vampire/E (need to check). We also need to be able to undo substitutions, so we keep a trail of variable bindings that we can backtrack on. The trail is fixed and never reallocated, we write over it every time we do a new unification. It consists in an array. The backtracking is done via a save():Int and restore(n:Int) functions that reset up to position n in the trail. The trail is passed arround after unification to build an applier that actually instantiates literals in the clause to build a new one. It is also used to build the proof object, but that can be done by reunifying also.

We also need to implement KBO (not LPO). This is non-trivial, the naive way to do it is inefficient. We should follow the paper "Things to Know when Implementing KBO" paper. We also follow Vampire and E.
Files: Core.scala, KBO.scala