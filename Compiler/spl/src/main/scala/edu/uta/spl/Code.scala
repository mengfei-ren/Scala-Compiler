/****************************************************************************************************
 *
 * File: Code.scala
 * The IR code generator for SPL programs
 *
 ****************************************************************************************************/

package edu.uta.spl


abstract class CodeGenerator ( tc: TypeChecker )  {
  def typechecker: TypeChecker = tc
  def st: SymbolTable = tc.st
  def code ( e: Program ): IRstmt
  def allocate_variable ( name: String, var_type: Type, fname: String ): IRexp
}


class Code ( tc: TypeChecker ) extends CodeGenerator(tc) {

  var name_counter = 0

  /** generate a new name */
  def new_name ( name: String ): String = {
    name_counter += 1
    name + "_" + name_counter
  }

  /** IR code to be added at the end of program */
  var addedCode: List[IRstmt] = Nil

  def addCode ( code: IRstmt* ) {
    addedCode ++= code
  }

  /** allocate a new variable at the end of the current frame and return the access code */
  def allocate_variable ( name: String, var_type: Type, fname: String ): IRexp =
    st.lookup(fname) match {
      case Some(FuncDeclaration(rtp,params,label,level,min_offset))
        => // allocate variable at the next available offset in frame
           st.insert(name,VarDeclaration(var_type,level,min_offset))
           // the next available offset in frame is 4 bytes below
           st.replace(fname,FuncDeclaration(rtp,params,label,level,min_offset-4))
           // return the code that accesses the variable
           Mem(Binop("PLUS",Reg("fp"),IntValue(min_offset)))
      case _ => throw new Error("No current function: " + fname)
    }

  /** access a frame-allocated variable from the run-time stack */
  def access_variable ( name: String, level: Int ): IRexp =
    st.lookup(name) match {
      case Some(VarDeclaration(_,var_level,offset))
        => var res: IRexp = Reg("fp")
           // non-local variable: follow the static link (level-var_level) times
           for ( i <- var_level+1 to level )
               res = Mem(Binop("PLUS",res,IntValue(-8)))
           Mem(Binop("PLUS",res,IntValue(offset)))
      case _ => throw new Error("Undefined variable: " + name)
    }

  /** return the IR code from the Expr e (level is the current function nesting level,
   *  fname is the name of the current function/procedure) */
  def code ( e: Expr, level: Int, fname: String ): IRexp =
    e match {
      case BinOpExp(op,left,right)
        => val cl = code(left,level,fname)
           val cr = code(right,level,fname)
           val nop = op.toUpperCase()
           Binop(nop,cl,cr)
      case ArrayGen(len,v)
        => val A = allocate_variable(new_name("A"),typechecker.typecheck(e),fname)
           val L = allocate_variable(new_name("L"),IntType(),fname)
           val V = allocate_variable(new_name("V"),typechecker.typecheck(v),fname)
           val I = allocate_variable(new_name("I"),IntType(),fname)
           val loop = new_name("loop")
           val exit = new_name("exit")
           ESeq(Seq(List(Move(L,code(len,level,fname)),   // store length in L
                         Move(A,Allocate(Binop("PLUS",L,IntValue(1)))),
                         Move(V,code(v,level,fname)),     // store value in V
                         Move(Mem(A),L),                  // store length in A[0]
                         Move(I,IntValue(0)),
                         Label(loop),                     // for-loop
                         CJump(Binop("GEQ",I,L),exit),
                         Move(Mem(Binop("PLUS",A,Binop("TIMES",Binop("PLUS",I,IntValue(1)),IntValue(4)))),V),  // A[i] = v
                         Move(I,Binop("PLUS",I,IntValue(1))),
                         Jump(loop),
                         Label(exit))),
                A)

      /* PUT YOUR CODE HERE */
	  case IntConst(v) => IntValue(v)
	  case FloatConst(v) => FloatValue(v)
	  case StringConst(v) => StringValue(v)
	  case BooleanConst(v) => {
		if(v) IntValue(1) else IntValue(0)
	  }
	  case LvalExp(v) => code(v,level,fname)
	  case NullExp() => IntValue(0)
	  
	  case UnOpExp(op,v) => {
		var c = code(v,level,fname)
		val uop = op.toUpperCase()
		Unop(uop,c)
	  }
	  
	  case CallExp(name,args) => {
		st.lookup(name) match {
			case Some(FuncDeclaration(_,_,label,clevel,_)) => {
				var stlink:IRexp = Reg("fp")
				for(i <- (clevel to level)) {
					stlink = Mem(Binop("PLUS",stlink,IntValue(-8)))
				}
				Call(name,stlink,args.map(x=>code(x,level,fname)))
			}
			case _ => throw new Error("Undefiend function: "+name)
		}
	  }
	  
	  case ArrayExp(elements) => {
		var tp = typechecker.typecheck(e)
		typechecker.expandType(tp) match {
			case ArrayType(atp) => {
				val len = elements.length
				val A = allocate_variable(new_name("A"),tp,fname)
				var elcodes:List[IRstmt] = Nil
				for(i<-0 until elements.length) {
					val el = elements.apply(i)
					var cel = code(el,level,fname)
					var index = i + 1
					elcodes = elcodes :+ Move(Mem(Binop("PLUS",A,IntValue(index*4))),cel)
				}
				val clen = code(IntConst(len),level,fname)
				ESeq(Seq(List(Move(A,Allocate(IntValue(len+1))),
							  Move(Mem(A),clen)
							 ):::elcodes),
					 A)
			}
			case _ => throw new Error("Illegal array expression: "+e)
		}
	  }
	  
	  case RecordExp(comps) => {
		var tp = typechecker.typecheck(e)
		typechecker.expandType(tp) match {
			case RecordType(params) => {
				val len = comps.length
				val clen = code(IntConst(len),level, fname)
				val R = allocate_variable(new_name("R"),tp,fname)
				var explist:List[IRexp] = Nil
				comps.foreach({
					case Bind(v,ex) => explist = explist :+ code(ex,level,fname)
				})
				var complist:List[IRstmt] = explist.map(irex => {
					val index = explist.indexOf(irex)
					Move(Mem(Binop("PLUS",R,IntValue(index*4))),irex)
				})
				ESeq(Seq(List(Move(R,Allocate(IntValue(len)))):::complist),
					 R)
			}
			case _ => throw new Error("Illegal record expression: " + e)
		}
	  }
	  
	  case TupleExp(elements) => {
		var tp = typechecker.typecheck(e)
		typechecker.expandType(tp) match {
			case TupleType(ttp) => {
				val len = elements.length
				val T = allocate_variable(new_name("T"),tp,fname)
				var elcodes:List[IRstmt] = elements.map(el=>{
					var cel = code(el,level,fname)
					var index = elements.indexOf(el)
					Move(Mem(Binop("PLUS",T,IntValue(index*4))),cel)
				})
				val clen = code(IntConst(len),level,fname)
				ESeq(Seq(List(Move(T,Allocate(IntValue(len+1)))):::elcodes),
					 T)
			}
			case _ => throw new Error("Illegal tuple expression: "+e)
		}
	  }
	  
      case _ => throw new Error("Wrong expression: "+e)
    }

  /** return the IR code from the Lvalue e (level is the current function nesting level,
   *  fname is the name of the current function/procedure) */
  def code ( e: Lvalue, level: Int, fname: String ): IRexp =
    e match {
     case RecordDeref(r,a)
        => val cr = code(r,level,fname)
           typechecker.expandType(typechecker.typecheck(r)) match {
              case RecordType(cl)
                => val i = cl.map(_.name).indexOf(a)
                   Mem(Binop("PLUS",cr,IntValue(i*4)))
              case _ => throw new Error("Unkown record: "+e)
           }

     /* PUT YOUR CODE HERE */
	 case Var(name) => name match {
		case "false" | "Nil" => IntValue(0)
		case "true" => IntValue(1)
		case _ => access_variable(name,level)
	 }
	 
	 case ArrayDeref(array,index) => {
		val carray = code(array,level,fname)
		val cindex = code(index,level,fname)
		typechecker.expandType(typechecker.typecheck(array)) match {
			case ArrayType(tp) => {
				Mem(Binop("PLUS",carray,Binop("TIMES",Binop("PLUS", cindex, IntValue(1)),IntValue(4))))
			}
			case _ => throw new Error("Unknown array value: "+e)
		}
	 }

	 case TupleDeref(tuple,index) => {
		val ctuple = code(tuple,level,fname)
		typechecker.expandType(typechecker.typecheck(tuple)) match {
			case TupleType(tp) => {
				Mem(Binop("PLUS",ctuple,IntValue(index*4)))
			}
			case _ => throw new Error("Unknown tuple value: "+e)
		}
	 }

     case _ => throw new Error("Wrong statement: " + e)
    }

  /** return the IR code from the Statement e (level is the current function nesting level,
   *  fname is the name of the current function/procedure)
   *  and exit_label is the exit label       */
  def code ( e: Stmt, level: Int, fname: String, exit_label: String ): IRstmt =
    e match {
      case ForSt(v,a,b,c,s)
        => val loop = new_name("loop")
           val exit = new_name("exit")
           val cv = allocate_variable(v,IntType(),fname)
           val ca = code(a,level,fname)
           val cb = code(b,level,fname)
           val cc = code(c,level,fname)
           val cs = code(s,level,fname,exit)
           Seq(List(Move(cv,ca),  // needs cv, not Mem(cv)
                    Label(loop),
                    CJump(Binop("GT",cv,cb),exit),
                    cs,
                    Move(cv,Binop("PLUS",cv,cc)),  // needs cv, not Mem(cv)
                    Jump(loop),
                    Label(exit)))

      /* PUT YOUR CODE HERE */
	  case AssignSt(dest,source) => {
		var cd = code(dest,level,fname)
		var cs = code(source,level,fname)
		Move(cd,cs)
	  }
	  
	  case CallSt(name,args) => {
		st.lookup(name) match {
			case Some(FuncDeclaration(_,_,label,clevel,_)) => {
				var rfp:IRexp = Reg("fp")
				for(i <- clevel to level) {
					rfp = Mem(Binop("PLUS",rfp,IntValue(-8)))
				}
				CallP(label,rfp,args.map(arg=>code(arg,level,fname)))
			}
			case _ => throw new Error("Unknown function: "+name)
		}
	  }
	  
	  case ReadSt(args) => {
		var st = args.map(arg => {
			var x = code(arg,level,fname)
			typechecker.typecheck(arg) match {
				case StringType() => SystemCall("READ_STRING",x)
				case FloatType() => SystemCall("READ_FLOAT",x)
				case IntType() => SystemCall("READ_INT",x)
				case _ => throw new Error("Unknown type"+typechecker.typecheck(arg))
			}
		})
		Seq(st)
	  }
	  
	  case PrintSt(args) => {
		var arglist: List[IRstmt] = List()
		for(i<-0 until args.length) {
			var arg = args.apply(i)
			var x = code(arg,level,fname)
			typechecker.typecheck(arg) match {
				case StringType() => arglist = arglist :+ SystemCall("WRITE_STRING",x)
				case FloatType() => arglist = arglist :+ SystemCall("WRITE_FLOAT",x)
				case IntType() => arglist = arglist :+ SystemCall("WRITE_INT",x)
				case _ => throw new Error("Expect primitive type in Print statement: "+e)
			}
		}
		arglist = arglist :+ SystemCall("WRITE_STRING",code(StringConst("\\n"),level,fname))
		Seq(arglist)
	  }
	  
	  case IfSt(cond,thenst,elsest) => {
		var trueL = new_name("trueL")
		var exit = new_name("exit")
		var ccond = code(cond,level,fname)
		var cthen = code(thenst,level,fname,exit_label)
		if(elsest != null) {
			var celse = code(elsest,level,fname,exit_label)
			Seq(List(CJump(ccond,trueL),
					 celse,
					 Jump(exit),
					 Label(trueL),
					 cthen,
					 Label(exit)))
		} else {
			Seq(List(CJump(ccond,trueL),
					 Seq(List()),
					 Jump(exit),
					 Label(trueL),
					 cthen,
					 Label(exit)))
		}
	  }
	  
	  case WhileSt(cond,body) => {
		var loop = new_name("loop")
		var exit = new_name("exit")
		var ccond = code(cond,level,fname)
		var cbody = code(body,level,fname,exit_label)
		Seq(List(Label(loop),
				 CJump(Unop("NOT",ccond),exit),
				 cbody,
				 Jump(loop),
				 Label(exit)))
	  }
	  
	  case LoopSt(body) => {
		var loop = new_name("loop")
		var exit = new_name("exit")
		var cbody = code(body,level,fname,exit_label)
		Seq(List(Label(loop),
				 cbody,
				 Jump(loop),
				 Label(exit)))
	  }
	  
	  case ExitSt() => { Jump(exit_label) }
	  
	  case ReturnValueSt(v) => {
		Seq(List(Move(Reg("a0"),code(v,level,fname)),
				 Move(Reg("ra"),Mem(Binop("PLUS",Reg("fp"),IntValue(-4)))),
                 Move(Reg("sp"),Reg("fp")),
                 Move(Reg("fp"),Mem(Reg("fp"))),
                 Return()))
	  }
	  
	  case ReturnSt() => {
		Seq(List(Move(Reg("ra"),Mem(Binop("PLUS",Reg("fp"),IntValue(-4)))),
                 Move(Reg("sp"),Reg("fp")),
                 Move(Reg("fp"),Mem(Reg("fp"))),
                 Return()))
	  }
	  
	  case BlockSt(decls,stmts) => {
	    var declist:List[IRstmt] = List()
		var stmtlist:List[IRstmt] = List()
		st.begin_scope()
		for(i<-0 until decls.length) {
			declist = declist :+ code(decls.apply(i),fname,level)
		}
		for(j<-0 until stmts.length){
			stmtlist = stmtlist :+ code(stmts.apply(j),level,fname,exit_label)
		}
		st.end_scope()
		Seq(declist ::: stmtlist)
	  }

      case _ => throw new Error("Wrong statement: " + e)
   }

  /** return the IR code for the declaration block of function fname
   * (level is the current function nesting level) */
  def code ( e: Definition, fname: String, level: Int ): IRstmt =
    e match {
      case FuncDef(f,ps,ot,b)
        => val flabel = if (f == "main") f else new_name(f)
           /* initial available offset in frame f is -12 */
           st.insert(f,FuncDeclaration(ot,ps,flabel,level+1,-12))
           st.begin_scope()
           /* formal parameters have positive offsets */
           ps.zipWithIndex.foreach{ case (Bind(v,tp),i)
                                      => st.insert(v,VarDeclaration(tp,level+1,(ps.length-i)*4)) }
           val body = code(b,level+1,f,"")
           st.end_scope()
           st.lookup(f) match {
             case Some(FuncDeclaration(_,_,_,_,offset))
               => addCode(Label(flabel),
                          /* prologue */
                          Move(Mem(Reg("sp")),Reg("fp")),
                          Move(Reg("fp"),Reg("sp")),
                          Move(Mem(Binop("PLUS",Reg("fp"),IntValue(-4))),Reg("ra")),
                          Move(Mem(Binop("PLUS",Reg("fp"),IntValue(-8))),Reg("v0")),
                          Move(Reg("sp"),Binop("PLUS",Reg("sp"),IntValue(offset))),
                          body,
                          /* epilogue */
                          Move(Reg("ra"),Mem(Binop("PLUS",Reg("fp"),IntValue(-4)))),
                          Move(Reg("sp"),Reg("fp")),
                          Move(Reg("fp"),Mem(Reg("fp"))),
                          Return())
                  Seq(List())
             case _ => throw new Error("Unkown function: "+f)
           }

      /* PUT YOUR CODE HERE */
	  case VarDef(name,hasType,value) => {
		var tp = typechecker.typecheck(value) 
		var dest:IRexp = null
		if (value == NullExp())
			dest = allocate_variable(name,hasType,fname)
		else if(hasType == null || hasType == AnyType())
			dest = allocate_variable(name,tp,fname)
		else {
			tp match {
				case RecordType(_) => tp = hasType
				case _ => tp = typechecker.typecheck(value)
			}
			if(hasType != tp)
				throw new Error("The Var definition does not match the required type: "+e)
			else dest = allocate_variable(name,hasType,fname)
		}
		Move(dest,code(value,level,fname))
	  }
	  
	  case TypeDef(name,isType) => {
		st.insert(name,TypeDeclaration(isType))
		Seq(List())
	  }

      case _ => throw new Error("Wrong statement: " + e)
    }

    def code ( e: Program ): IRstmt =
      e match {
        case Program(b@BlockSt(_,_))
          => st.begin_scope()
             val res = code(FuncDef("main",List(),NoType(),b),"",0)
             st.end_scope()
             Seq(res::addedCode)
        case _ => throw new Error("Wrong program "+e);
      }
}
