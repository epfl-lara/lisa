import ap.SimpleAPI
import ap.parser._
import lisa.utils.K
import lisa.utils.K.{given_Conversion_Identifier_String}
import IExpression._
import ap.proof.certificates.Certificate

object Princess {

    def main(args: Array[String]): Unit ={
        SimpleAPI.withProver(dumpScala=true) { p =>
            import p._
            setConstructProofs(true)
            setConstructProofs(false)

            println("Solving riddle ...")

            val a, b, c = createBooleanVariable
            val P = createRelation("P", 1)
            val Q = createRelation("Q", 2)

            setConstructProofs(true)

            //!!(!(a & (b | c)) & ((a & b) | (a & c)))

            //println(ex(y => all((IVariable(0) === y) <=> P(IVariable(0))) & Q(y, IVariable(0))))


            val x = K.variable
            val y = K.variable
            val z = K.variable
            val P1 = K.predicate(1)
            val Q1 = K.predicate(2)
            val form = {
                import lisa.utils.K.{given, *}
                val unders = Example.fixedPointDoubleApplication.goal.underlying
                PrincessEnvironment(p).formulaLisa2Princess((unders.left.head ==> forall(x, unders.right.head)))
            }
            val form2 = all(P(IVariable(0)) & ex( or(List(Q(IVariable(1), IVariable(0)), IVariable(1) === IVariable(0))) ))
            println(form)
            //println(form2)
            ??(form)
            println(???)
            println(getCertificate)
            getCertificate match
                case _ => ()
            
            
            println(certificateAsString(Map.empty, ap.parameters.Param.InputFormat.Princess))
            println("Inspection")
            

            //println(getInterpolants(List(Set(1, 3), Set(2))))

        }
    }


    class PrincessEnvironment(p:SimpleAPI){
    
        import p.{??? => PrincessProof, *}
        import scala.collection.mutable.HashMap


        //val termL2P_Map : HashMap[K.Term, ITerm] = HashMap.empty
        //val termP2L_Map : HashMap[ITerm, K.Term] = HashMap.empty

        val functionL2P_Map : HashMap[K.TermLabel, IFunction] = HashMap.empty
        val functionP2L_Map : HashMap[IFunction, K.TermLabel] = HashMap.empty
        val predicateL2P_Map : HashMap[K.PredicateLabel, Predicate] = HashMap.empty
        val predicateP2L_Map : HashMap[Predicate, K.PredicateLabel] = HashMap.empty

        /**
          * Create and memoize function symbols between a LISA function and its Princess counterpart
          */ 
        def functionLisa2Princess(fun: K.TermLabel): IFunction = {
            functionL2P_Map.get(fun) match
                case Some(value) => return value
                case None => 
                    val newf = createFunction(fun.id, fun.arity)
                    functionL2P_Map.update(fun, newf)
                    functionP2L_Map.update(newf, fun)
                    newf
        }        
        /**
          * Create and memoize predicate symbols between a LISA predicate and its Princess counterpart
          */ 
        def relationLisa2Princess(pred: K.PredicateLabel): Predicate = {
            predicateL2P_Map.get(pred) match
                case Some(value) => return value
                case None => 
                    val newf = createRelation(pred.id, pred.arity)
                    predicateL2P_Map.update(pred, newf)
                    predicateP2L_Map.update(newf, pred)
                    newf
        }

        /**
          * Create and memoize terms between a LISA term and its Princess counterpart
          */ 
        def termLisa2Princess(term: K.Term, depth:Int, vMap:Map[K.Identifier, Int]): ITerm = {
            /*termL2P_Map.get(term) match
                case Some(value) => return value
                case None => ()*/
            val K.Term(label, args) = term
            val output: ITerm = label match
                case f : (K.ConstantFunctionLabel | K.SchematicFunctionLabel) => 
                    functionLisa2Princess(f)(args.map(termLisa2Princess(_, depth, vMap))*)
                case K.VariableLabel(id) => IVariable(depth-vMap(id))
            
            //termL2P_Map.update(term, output)
            //termP2L_Map.update(output, term)
            output
        }



        val formulaL2P_Map : HashMap[K.Formula, IFormula] = HashMap.empty
        val formulaP2L_Map : HashMap[IFormula, K.Formula] = HashMap.empty

        /**
          * Create and memoize formulas between a LISA formula and its Princess counterpart
          */ 
        def formulaLisa2Princess(formula: K.Formula, depth:Int = 0, vMap:Map[K.Identifier, Int] = Map.empty): IFormula = {

            formulaL2P_Map.get(formula) match
                case Some(value) => return value
                case None => ()
            
            val output = formula match
                case K.BinderFormula(label, bound, inner) => label match
                    case K.Exists => ex(formulaLisa2Princess(inner, depth+1, vMap + (bound.id -> (depth+1))))
                    case K.ExistsOne => 
                        ex(all(
                            (IVariable(0) === IVariable(1)) <=> formulaLisa2Princess(inner, depth+2, vMap + (bound.id -> (depth+2)))
                        ))
                    case K.Forall => all(formulaLisa2Princess(inner, depth+1, vMap + (bound.id -> (depth+1)))) 

                case K.ConnectorFormula(label, args) => label match
                    case K.SchematicConnectorLabel(id, arity) =>  ???
                    case K.And => and(args.map(formulaLisa2Princess(_, depth, vMap)))
                    case K.Iff => 
                        val f1 = formulaLisa2Princess(args.head, depth, vMap)
                        val f2 = formulaLisa2Princess(args.tail.head, depth, vMap)
                        and(List(or(List(!f1, f2)), or(List(!f2, f1))))
                    case K.Implies => 
                        or(List(!formulaLisa2Princess(args.head, depth, vMap), formulaLisa2Princess(args.tail.head, depth, vMap)))
                    case K.Neg => !formulaLisa2Princess(args.head, depth, vMap)
                    case K.Or => or(args.map(formulaLisa2Princess(_, depth, vMap)))
                
                case K.PredicateFormula(label, args) => 
                    if (label == K.equality) IEquation(termLisa2Princess(args.head, depth, vMap), termLisa2Princess(args(1), depth, vMap))
                    else relationLisa2Princess(label)(args.map(termLisa2Princess(_, depth, vMap))*)
            formulaL2P_Map.update(formula, output)
            formulaP2L_Map.update(output, formula)
            output

        }
    }



    def CertificatePrincess2Lisa(c:Certificate) : Unit = ()




}
