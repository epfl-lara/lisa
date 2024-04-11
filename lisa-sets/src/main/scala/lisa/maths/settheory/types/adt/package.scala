package lisa.maths.settheory.types

/**
  * Provides definitional mechanisms for Algebraic Data Types (ADTs) and tactics for reasoning about them.
  *
  * ===Usage===
  *
  * In order to use ADTs, you need to import 
  * {{{
  *   lisa.maths.settheory.types.adt.{*, given}
  * }}}
  * 
  * ====Defining an ADT====
  *
  * ADTs can be defined using the following syntax:
  * {{{
  *   val define(adtName: ADT, constructors(c1, ..., cn)) = (T1, ..., Tn) | ... | (S1, ..., Sm)
  * }}}
  * 
  * where `adtName` is the identifier of the ADT,`c1 ... cn` are the identifiers of the different constructors of the ADT,
  * and `T1, ..., Tn, S1, ..., Sm` are the types defining the signature of each constructor.
  * Note that adtName and `c1 ... cn` are scala identifiers, respectively referring to the ADT and the constructors.
  * In addition, you cannot define two ADT with the same name, even in different scopes, as they introduce a new global definition.
  * Here are some examples of ADT definitions:
  * {{{
  *   val define(bool: ADT, constructors(tru, fals)) = () | ()
  *   val define(option: ADT, constructors(none, some)) = () | A
  *   val define(list: ADT, constructors(nil, cons)) = () | (A, list)
  *   val define(nat: ADT, constructors(zero, succ)) = () | nat
  * }}}
  *   
  * 
  * 
  
  */
package object adt {
  export ADTSyntax.{ |, define, constructors, adt_to_term, fun_to_term, constructor_to_term, Case, fun, -->, apply}
  export ADTSyntax.ADTBuilder.|
  export lisa.maths.settheory.types.TypeSystem.*
}

