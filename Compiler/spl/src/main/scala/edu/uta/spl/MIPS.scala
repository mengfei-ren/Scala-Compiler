/****************************************************************************************************
 *
 * File: MIPS.scala
 * Generation of MIPS code from IR code
 *
 ****************************************************************************************************/

package edu.uta.spl

/** representation of a MIPS register */
case class Register ( reg: String ) {
    override def toString: String = reg
}


/** a pool of available registers */
class RegisterPool {

  val all_registers
        = List( "$t0", "$t1", "$t2", "$t3", "$t4", "$t5", "$t6", "$t7", "$t8", "$t9",
                "$s0", "$s1", "$s2", "$s3", "$s4", "$s5", "$s6", "$s7" )

  var available_registers: List[Register] = all_registers.map(Register)

  /** is register reg temporary? */
  def is_temporary ( reg: Register ): Boolean =
    reg match {
      case Register(n) => all_registers.contains(n)
    }

  /** return the next available temporary register */
  def get (): Register =
    available_registers match {
      case reg::rs
        => available_registers = rs
           reg
      case _ => throw new Error("*** Run out of registers")
    }

  /** recycle (put back into the register pool) the register reg (if is temporary) */
  def recycle ( reg: Register ) {
    if (available_registers.contains(reg))
       throw new Error("*** Register has already been recycled: "+reg)
    if (is_temporary(reg))
       available_registers = reg::available_registers
  }

  /** return the list of all temporary registers currently in use */
  def used (): List[Register] = {
    for ( reg <- all_registers if !available_registers.contains(Register(reg)) )
        yield Register(reg)
  }
}


abstract class MipsGenerator {
  def clear ()
  def emit ( e: IRstmt )
  def initialCode ()
}


class Mips extends MipsGenerator {
 
  /** emit a MIPS label */
  def mips_label ( s: String ) {
    SPL.out.println(s + ":")
  }

  /** emit MIPS code with no operands */
  def mips ( op: String ) {
    SPL.out.println("        " + op)
  }

  /** emit MIPS code with operands */
  def mips ( op: String, args: String ) {
    SPL.out.print("        " + op)
    for ( i <- op.length to 10)
        SPL.out.print(" ")
    SPL.out.println(args)
  }

  /** a pool of temporary registers */
  var rpool = new RegisterPool

  /** clear the register pool */
  def clear {
    rpool = new RegisterPool
  }

  var name_counter = 0

  /** generate a new  label name */
  def new_label (): String = {
    name_counter += 1
    "L_" + name_counter
  }

  /** generate MIPS code from the IR expression e and return the register that will hold the result */
  def emit ( e: IRexp ): Register = {
    e match {
      case Mem(Binop("PLUS",Reg(r),IntValue(n)))
        => val reg = rpool.get()
           mips("lw",reg + ", " + n + "($" + r + ")")
           reg
      case Binop("AND",x,y)
        => val label = new_label()
           val left = emit(x)
           val reg = left
           mips("beq",left+", 0, "+label)
           val right = emit(y)
           mips("move",left+", "+right)
           mips_label(label)
           rpool.recycle(right)
           reg
      case Call(f,sl,args)
        => val used_regs = rpool.used()
           val size = (used_regs.length+args.length)*4
           /* allocate space for used temporary registers */
           if (size > 0)
              mips("subu","$sp, $sp, "+size)
           /* push the used temporary registers */
           var i = size
           for (r <- used_regs) {
               mips("sw",r + ", " + i + "($sp)")
               i -= 4
           }
           /* push arguments */
           i = args.length*4
           for (a <- args) {
              val reg = emit(a)
              mips("sw",reg + ", " + i + "($sp)")
              rpool.recycle(reg)
              i -= 4
           }
           /* set $v0 to be the static link */
           val sreg = emit(sl)
           mips("move","$v0, " + sreg)
           rpool.recycle(sreg)
           mips("jal",f)
           i = size
           /* pop the used temporary registers */
           for (r <- used_regs) {
              mips("lw",r + ", " + i + "($sp)")
              i -= 4
           }
           /* deallocate stack from args and used temporary registers */
           if (size > 0)
              mips("addu","$sp, $sp, "+size)
           val res = rpool.get()
           mips("move",res + ", $a0")
           /* You shouldn't just return $a0 */
           res

      /* PUT YOUR CODE HERE */
	  case Mem(Binop("PLUS",x,IntValue(n))) => {
		val reg = rpool.get()
		val xreg = emit(x)
	    mips("lw",reg + ", " + n + "(" + xreg + ")")
		rpool.recycle(xreg)
        reg
	  }
	  
	  case Binop("OR",x,y) => {
		val label = new_label()
	    val left = emit(x)
	    val reg = left
	    mips("beq",left+", 1, "+label)
	    val right = emit(y)
	    mips("move",left+", "+right)
	    mips_label(label)
	    rpool.recycle(right)
	    reg
	  }
	  
	  case Binop("PLUS",Reg(x),y) => {
		val right = emit(y)
		val reg = rpool.get()
		mips("addu", reg + ", $" + x + ", " + right)
		rpool.recycle(right)
		reg
	  }
	  
	  case Binop("PLUS",x,y) => {
		val left = emit(x)
		val right = emit(y)
		var reg = left
		mips("addu", reg + ", " + left + ", " + right)
		rpool.recycle(right)
		reg
	  }
	  
	  case Binop("MINUS",x,y) => {
		val left = emit(x)
		val right = emit(y)
		var reg = left
		mips("subu", reg + ", " + left + ", " + right)
		rpool.recycle(right)
		reg
	  }
	  
	  case Binop("TIMES",x,y) => {
		val left = emit(x)
		val right = emit(y)
		var reg = left
		mips("mul", reg + ", " + left + ", " + right)
		rpool.recycle(right)
		reg
	  }
	  
	  case Binop("DIV",x,y) => {
		val left = emit(x)
		val right = emit(y)
		var reg = left
		mips("div", reg + ", " + left + ", " + right)
		rpool.recycle(right)
		reg
	  }
	  
	  case Binop("MOD",x,y) => {
		val left = emit(x)
		val right = emit(y)
		var reg = left
		mips("rem", reg + ", " + left + ", " + right)
		rpool.recycle(right)
		reg
	  }
	  
	  case Binop("EQ",x,y) => {
		val left = emit(x)
		val right = emit(y)
		var reg = left
		mips("seq", reg + ", " + left + ", " + right)
		rpool.recycle(right)
		reg
	  }
	  
	  case Binop("NEQ",x,y) => {
		val left = emit(x)
		val right = emit(y)
		var reg = left
		mips("sne", reg + ", " + left + ", " + right)
		rpool.recycle(right)
		reg
	  }
	  
	  case Binop("LT",x,y) => {
		val left = emit(x)
		val right = emit(y)
		var reg = left
		mips("slt", reg + ", " + left + ", " + right)
		rpool.recycle(right)
		reg
	  }
	  
	  case Binop("LEQ",x,y) => {
		val left = emit(x)
		val right = emit(y)
		var reg = left
		mips("sle", reg + ", " + left + ", " + right)
		rpool.recycle(right)
		reg
	  }
	  
	  case Binop("GT",x,y) => {
		val left = emit(x)
		val right = emit(y)
		var reg = left
		mips("sgt", reg + ", " + left + ", " + right)
		rpool.recycle(right)
		reg
	  }
	  
	  case Binop("GEQ",x,y) => {
		val left = emit(x)
		val right = emit(y)
		var reg = left
		mips("sge", reg + ", " + left + ", " + right)
		rpool.recycle(right)
		reg
	  }
	  
	  case Unop("NOT",x) => {
		val left = emit(x)
		var reg = left
		mips("seq", reg + ", " + left + ", " + 0)
		reg
	  }
	  
	  case Unop("MINUS",x) => {
		val left = emit(x)
		var reg = left
		mips("neg", reg + ", " + left)
		reg
	  }
	  
	  case IntValue(x) => {
		val reg = rpool.get()
		mips("li", reg + ", " + x)
		reg
	  }
	  
	  case FloatValue(x) => {
		val reg = rpool.get()
		mips("li", reg + ", " + x)
		reg
	  }
	  
	  case StringValue(x) => {
		val reg = rpool.get()
		val label = new_label()
		mips(".data")
		mips(".align", "2")
		mips_label(label)
		mips(".asciiz", "\"" + x + "\"")
		mips(".text")
		mips("la", reg + ", " + label)
		reg
	  }
	  
	  case Mem(Reg(r)) => {
		var reg = rpool.get()
		mips("lw", reg + ", ($" + r + ")")
		reg
	  }
	  
	  case Mem(a) => {
		val reg = rpool.get()
		val xreg = emit(a)
		mips("lw", reg + ", (" + xreg + ")")
		rpool.recycle(xreg)
		reg 
	  }
	  
	  case Reg(r) => { Register("$" + r) }
	  
	  case Allocate(x) => {
		val l = emit(Binop("TIMES", x, IntValue(4)))
		var reg = rpool.get()
		mips("move", reg + ", $gp")
		mips("addu", "$gp, $gp, " + l)
		rpool.recycle(l)
		reg
	  }
	  
      case _ => throw new Error("*** Unknown IR: "+e)
    }
  }

  /** generate MIPS code from the IR statement e */
  def emit ( e: IRstmt ) {
    e match {
      case Move(Mem(Binop("PLUS",Reg(r),IntValue(n))),u)
        => val src = emit(u)
           mips("sw",src + ", " + n + "($" + r + ")")
           rpool.recycle(src)

      /* PUT YOUR CODE HERE */
	  case Move(Mem(Binop("PLUS", x, IntValue(n))),y) => {
		val xreg = emit(x)
		val yreg = emit(y)
		mips("sw",yreg + ", " + n + "(" + xreg + ")")
		rpool.recycle(xreg)
		rpool.recycle(yreg)
	  }
	  
	  case Move(Mem(Reg(r)),x) => {
		val reg = emit(x)
		mips("sw", reg + ", ($" + r + ")")
		rpool.recycle(reg)
	  }
	  
	  case Move(Mem(a),x) => {
		val areg = emit(a)
		val xreg = emit(x)
		mips("sw", xreg + ", (" + areg + ")")
		rpool.recycle(areg)
		rpool.recycle(xreg)
	  }
	  
	  case Move(Reg(x),Reg(y)) => { mips("move", "$" + x + ", $" + y) }
	  
	  case Move(Reg(r),IntValue(x)) => { mips("li", "$" + r + ", " + x) }
	  
	  case Move(Reg(r), Mem(Binop("PLUS",x,IntValue(y)))) => {
		val reg = emit(x)
		mips("lw", "$" + r + ", " + y + "(" + reg + ")")
		rpool.recycle(reg)
	  }
	  
	  case Move(Reg(r),Mem(a)) => {
	    val reg = emit(a)
		mips("lw", "$" + r +", (" + reg + ")")
		rpool.recycle(reg)
	  }
	  
	  case Move(Reg(r),x) => {
		val xreg = emit(x)
		var reg = Register(r)
		if(reg == xreg)
			reg = rpool.get()
		mips("move", "$" + r + ", " + xreg)
		rpool.recycle(xreg)
	  }
	  
	  case Label(x) => mips_label(x)
	  
	  case Jump(a) => mips("j",a)
	  
	  case CJump(x,a) => {
		val reg = emit(x)
		mips("beq", reg + ", 1, " + a)
		rpool.recycle(reg)
	  }
	  
	  case SystemCall("READ_INT",Mem(x)) => {
		val reg = emit(x)
		mips("li", "$v0, 5")
        mips("syscall")
        mips("sw", "$v0, (" + reg + ")")
	  }
	  
	  case SystemCall("READ_FLOAT",Mem(x)) => {
		val reg = emit(x)
		mips("li", "$v0, 6")
        mips("syscall")
        mips("sw", "$v0, (" + reg + ")")
	  }
	  
	  case SystemCall("READ_STRING",Mem(x)) => {
		val reg = emit(x)
		mips("li", "$v0, 8")
        mips("syscall")
        mips("sw", "$a1, (" + reg + ")")
        mips("sw", "$a0, 4(" + reg+ ")")
        rpool.recycle(reg);
	  }
	  
	  case SystemCall("WRITE_INT",x) => {
		mips("move", "$a0, " + emit(x))
		mips("li", "$v0, " + 1)
		mips("syscall")
	  }
	  
	  case SystemCall("WRITE_FLOAT",x) => {
		mips("move", "$f12, " + emit(x))
        mips("li", "$v0, " + 2)
        mips("syscall")
	  }
	  
	  case SystemCall("WRITE_STRING",StringValue("\\n")) => {
		mips("li", "$v0, 4")
        mips("la", "$a0, ENDL_")
        mips("syscall")
	  }
	  
	  case SystemCall("WRITE_STRING",x) => {
		mips("move", "$a0, " + emit(x))
        mips("li", "$v0, " + 4)
        mips("syscall")
	  }
	  
	  case CallP(fname,stlink,args) => {
		val used_regs = rpool.used()
	    val size = (used_regs.length + args.length) * 4
	    
		if (size > 0)
		  mips("subu","$sp, $sp, " + size)
		
		var i = size
		for (r <- used_regs) {
		   mips("sw",r + ", " + i + "($sp)")
		   i -= 4
		}
		i = args.length*4
		
		for (a <- args) {
		  val reg = emit(a)
		  mips("sw",reg + ", " + i + "($sp)")
		  rpool.recycle(reg)
		  i -= 4
		}
		val sreg = emit(stlink)
		mips("move","$v0, " + sreg)
		rpool.recycle(sreg)
		mips("jal",fname)
		i = size
		for (r <- used_regs) {
		  mips("lw",r + ", " + i + "($sp)")
		  i -= 4
		}
		if (size > 0)
		  mips("addu","$sp, $sp, "+size)
	  }
	  
	  case Return() => { mips("jr","$ra") }

      case _ => throw new Error("*** Unknown IR "+e)
    }
  }

  /** generate initial MIPS code from the program */
  def initialCode () {
    mips(".globl","main")
    mips(".data")
    mips_label("ENDL_")
    mips(".asciiz","\"\\n\"")
    mips(".text")
  }
}
