package edu.uta.spl

abstract class TypeChecker {
  var trace_typecheck = false

  /** symbol table to store SPL declarations */
  var st = new SymbolTable

  def expandType ( tp: Type ): Type
  def typecheck ( e: Expr ): Type
  def typecheck ( e: Lvalue ): Type
  def typecheck ( e: Stmt, expected_type: Type )
  def typecheck ( e: Definition )
  def typecheck ( e: Program )
}


class TypeCheck extends TypeChecker {

  /** typechecking error */
  def error ( msg: String ): Type = {
    System.err.println("*** Typechecking Error: "+msg)
    System.err.println("*** Symbol Table: "+st)
    System.exit(1)
    null
  }

  /** if tp is a named type, expand it */
  def expandType ( tp: Type ): Type =
    tp match {
      case NamedType(nm)
        => st.lookup(nm) match {
          case Some(TypeDeclaration(t))
              => expandType(t)
          case _ => error("Undeclared type: "+tp)
        }
      case _ => tp
  }

  /** returns true if the types tp1 and tp2 are equal under structural equivalence */
  def typeEquivalence ( tp1: Type, tp2: Type ): Boolean =
    if (tp1 == tp2 || tp1.isInstanceOf[AnyType] || tp2.isInstanceOf[AnyType])
      true
    else expandType(tp1) match {
      case ArrayType(t1)
        => expandType(tp2) match {
              case ArrayType(t2)
                => typeEquivalence(t1,t2)
              case _ => false
           }
      case RecordType(fs1)
        => expandType(tp2) match {
              case RecordType(fs2)
                => fs1.length == fs2.length &&
                   (fs1 zip fs2).map{ case (Bind(v1,t1),Bind(v2,t2))
                                        => v1==v2 && typeEquivalence(t1,t2) }
                                .reduce(_&&_)
              case _ => false
           }
      case TupleType(ts1)
        => expandType(tp2) match {
              case TupleType(ts2)
                => ts1.length == ts2.length &&
                   (ts1 zip ts2).map{ case (t1,t2) => typeEquivalence(t1,t2) }
                                .reduce(_&&_)
              case _ => false
           }
      case _
        => tp2 match {
             case NamedType(n) => typeEquivalence(tp1,expandType(tp2))
             case _ => false
           }
    }

  /* tracing level */
  var level: Int = -1

  /** trace typechecking */
  def trace[T] ( e: Any, result: => T ): T = {
    if (trace_typecheck) {
       level += 1
       println(" "*(3*level)+"** "+e)
    }
    val res = result
    if (trace_typecheck) {
       print(" "*(3*level))
       if (e.isInstanceOf[Stmt] || e.isInstanceOf[Definition])
          println("->")
       else println("-> "+res)
       level -= 1
    }
    res
  }

  /** typecheck an expression AST */
  def typecheck ( e: Expr ): Type =
    trace(e,e match {
      case BinOpExp(op,l,r)
        => val ltp = typecheck(l)
           val rtp = typecheck(r)
           if (!typeEquivalence(ltp,rtp))
              error("Incompatible types in binary operation: "+e)
           else if (op.equals("and") || op.equals("or"))
                   if (typeEquivalence(ltp,BooleanType()))
                      ltp
                   else error("AND/OR operation can only be applied to booleans: "+e)
           else if (op.equals("eq") || op.equals("neq"))
                   BooleanType()
           else if (!typeEquivalence(ltp,IntType()) && !typeEquivalence(ltp,FloatType()))
                   error("Binary arithmetic operations can only be applied to integer or real numbers: "+e)
           else if (op.equals("gt") || op.equals("lt") || op.equals("geq") || op.equals("leq"))
                   BooleanType()
           else ltp

      /* PUT YOUR CODE HERE */
	  case IntConst(i) => IntType()
      case FloatConst(r) => FloatType()
      case StringConst(s) => StringType()
	  case BooleanConst(s) => BooleanType()
      case LvalExp(le) => typecheck(le)
	  case NullExp() => AnyType()
	  
	  case UnOpExp(op,od) => {
		var utp = typecheck(od)
		if(op.equals("minus"))
			if(!typeEquivalence(utp, IntType()) && !typeEquivalence(utp, FloatType()))
				throw new Error("Unary operation - can only be applied to integer or real numbers: " + e)
			else utp
		else if (op.equals("not"))
			if(!typeEquivalence(utp, BooleanType()) )
				throw new Error("Unary operation NOT can only be applied to booleans: " + e)
			else utp
		else NoType()
	  }
      
	  case CallExp(name,args) => {
		st.lookup(name) match {
			case Some(FuncDeclaration(otp,params,"",0,0)) => {
				if(args.length != params.length)
					throw new Error("Number of parameters does not match the number of arguments: " + e)
				
				args.map(arg => typecheck(arg)).zip(params).map(m => {
					var tpx = m._1
					var tpy = m._2 match { case Bind(_,tp) => tp }
					if (!typeEquivalence(tpx,tpy))
						throw new Error("Type of argument "+tpx+" does not match type of parameter: "+tpy)
				})
				
				otp
			}
			case _ => throw new Error("Undefiend function: "+name)
		}
	  }
	  
	  case RecordExp(comps) => {
		var tpList:List[Bind[Type]] = List()
		comps.foreach({
			case Bind(v,ex) => {
				var tpBind:Bind[Type] = Bind(v,typecheck(ex))
				tpList = tpList :+ tpBind
			}
		})
		RecordType(tpList)
	  }
	  
	  case TupleExp(args) => {
		var tpList:List[Type] = List()
		args.foreach(arg => {
			tpList = tpList :+ typecheck(arg)
		})
		TupleType(tpList)
	  }
	  
	  case ArrayExp(args) => {
		var tp = typecheck(args.head)
		for(index <- 1 until args.length) {
			if(!typeEquivalence(typecheck(args.apply(index)),tp))
				throw new Error("The elements in an array should have the same type: " + e)
		}
		ArrayType(tp)
	  }
	  
	  case ArrayGen(len,vl) => {
		var length = typecheck(len)
		var valuetp = typecheck(vl)
		if(!typeEquivalence(length,IntType()))
			error("The length of array must be integer" + e)
		else ArrayType(valuetp)
	  }
	  
	  case _ => throw new Error("Wrong expression: "+e)
    } )

  /** typecheck an Lvalue AST */
  def typecheck ( e: Lvalue ): Type =
    trace(e,e match {
      case Var(name)
        => st.lookup(name) match {
              case Some(VarDeclaration(t,_,_)) => t
              case Some(_) => error(name+" is not a variable")
              case None => error("Undefined variable: "+name)
        }

      /* PUT YOUR CODE HERE */
	  case ArrayDeref(name,index) => {
		if(!typeEquivalence(typecheck(index),IntType()))
			throw new Error("Array index must be integer: " + e)
		expandType(typecheck(name)) match {
			case ArrayType(tp) => tp
			case _ => throw new Error("Array indexing could only be done on an array: " + e)
		}
	  }
	  
	  case RecordDeref(name,attr) => {
		expandType(typecheck(name)) match {
			case RecordType(comps) => {
				var attrList:List[String] = List()
				comps.foreach({
					case Bind(v,_) => attrList = attrList :+ v
				})
				if(!attrList.contains(attr))
					throw new Error("The attribute is invalid in this Record value: "+attr)
				else {
					var index = attrList.indexOf(attr,0)
					comps(index).value
				}
			}
			case _ => throw new Error("Record projection can only be done on records: " + e)
		}
	  }
	  
	  case TupleDeref(name,index) => {
		expandType(typecheck(name)) match {
			case TupleType(t) => {
				t match {
					case List(tp) => TupleType(List(typecheck(name)))
					case _ => throw new Error("TupleDeref units is not valid: "+e)
				}
			}
			case _ => throw new Error("Tuple indexing can only be done on tuples:" + e)
		}
	  }
	  
      case _ => throw new Error("Wrong lvalue: "+e)
    } )

  /** typecheck a statement AST using the expected type of the return value from the current function */
  def typecheck ( e: Stmt, expected_type: Type ) {
    trace(e,e match {
      case AssignSt(d,s)
        => if (!typeEquivalence(typecheck(d),typecheck(s)))
              error("Incompatible types in assignment: "+e)

      /* PUT YOUR CODE HERE */
	  case CallSt(name, args) => {
		st.lookup(name) match {
			case Some(FuncDeclaration(otp,params,_,0,0)) => {
				if(args.length != params.length)
					throw new Error("Numbers of parameters does not match number of arguments:" + e)
				else {
					args.map(arg => typecheck(arg)).zip(params).map(m => {
					var tpx = m._1
					var tpy = m._2 match { case Bind(_,tp) => tp }
					if (!typeEquivalence(tpx,tpy))
						throw new Error("Type of argument "+tpx+" does not match type of parameter: "+tpy)
					})	
				}
				otp
			}	
						
			case _ => throw new Error("Undefined function: " + name)
		}
	  } 
	  
	  case ReadSt(args) => {
		args.foreach(arg => {
			var tp = typecheck(arg)
			if(!typeEquivalence(tp, BooleanType()) && !typeEquivalence(tp, IntType()) 
			&& !typeEquivalence(tp, FloatType()) && !typeEquivalence(tp, StringType()))
				throw new Error("Expect primitive type in READ statement: "+e)
		})
	  }
	  
	  case PrintSt(args) => {
		args.foreach(arg => {
			var tp = typecheck(arg)
			if(!typeEquivalence(tp, BooleanType()) && !typeEquivalence(tp, IntType()) 
			&& !typeEquivalence(tp, FloatType()) && !typeEquivalence(tp, StringType()))
				throw new Error("Expect primitive type in Print statement: "+e)
		})
	  }
	  
	  case IfSt(condtion,then_stmt,else_stmt) => {
		if(!typeEquivalence(typecheck(condtion),BooleanType()))
			throw new Error("Expect a boolean value in IF test" + condtion)
		typecheck(then_stmt, expected_type)
		if(else_stmt != null)
			typecheck(else_stmt, expected_type)
	  }
	  
	  case WhileSt(cond,body) => {
		if(!typeEquivalence(typecheck(cond),BooleanType()))
			throw new Error("Expect a boolean value in IF test" + cond)
		typecheck(body,expected_type)
	  }
	  
	  case LoopSt(body) => {
		typecheck(body,expected_type)
	  }
	  
	  case ForSt(variable,init,step,incr,body) => {
		if(!typeEquivalence(typecheck(init),IntType()))
			throw new Error("Initial value in FOR loop must be integer:"+init)
		if(!typeEquivalence(typecheck(step),IntType()))
			throw new Error("Step in FOR loop must be integer:"+step)
		if(!typeEquivalence(typecheck(incr),IntType()))
			throw new Error("The increment for each step in FOR loop must be integer:"+incr)
		st.begin_scope()
		st.insert(variable,VarDeclaration(IntType(),0,0))
		typecheck(body,expected_type)
		st.end_scope()
	  }
	  
	  case ExitSt() => {}
	  
	  case ReturnValueSt(value) => {
		if(!typeEquivalence(expected_type, NoType())) {
			var tp = typecheck(value)
			if(!typeEquivalence(tp, expected_type))
			throw new Error("Expect a return value with a different type: "+e)
		}
		else 
			throw new Error("Return type should be void: "+e)
	  }
	  
	  case ReturnSt() => {
		if(!typeEquivalence(expected_type, NoType()))
			throw new Error("Return type should be void: "+e)
	  }
	  
	  case BlockSt(decls,stmts) => {
		st.begin_scope()
		decls.foreach(decl => typecheck(decl))
		stmts.foreach(stmt => typecheck(stmt,expected_type))
		st.end_scope()
	  }
	  
      case _ => throw new Error("Wrong statement: "+e)
    } )
  }

  /** typecheck a definition */
  def typecheck ( e: Definition ) {
    trace(e,e match {
      case FuncDef(f,ps,ot,b)
        => st.insert(f,FuncDeclaration(ot,ps,"",0,0))
           st.begin_scope()
           ps.foreach{ case Bind(v,tp) => st.insert(v,VarDeclaration(tp,0,0)) }
           typecheck(b,ot)
           st.end_scope()

      /* PUT YOUR CODE HERE */
	  case TypeDef(t,isType) => {
		st.insert(t,TypeDeclaration(isType))
	  }
	  
	  case VarDef(v,hasType,value) => {
		var tp = typecheck(value)
		tp match {
			case AnyType() => st.insert(v,VarDeclaration(tp,0,0))
			case _ => {
				if(!typeEquivalence(hasType,tp))
					throw new Error("The Var definition does not match the required type: "+e)
				else
					st.insert(v,VarDeclaration(tp,0,0))
			}		
		}
	  }
	  
      case _ => throw new Error("Wrong statement: "+e)
    } )
  }

  /** typecheck the main program */
  def typecheck ( e: Program ) {
    typecheck(e.body,NoType())
  }
}
