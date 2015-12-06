#include "stdafx.h"

/******* Experiments TR-IDSIA-20-02: Optimal Ordered Problem Solver*/
/** Also in: Machine Learning vol 54 p 211-254, 2004 (OOPS) ********/
/** Also in: NIPS 15 p. 1571 - 1578, MIT Press, 2003 ***************/
/******* *********** Copyright (C):  Prof Dr Juergen Schmidhuber ***/
/******* *********** *************** http://www.idsia.ch/~juergen **/
/******* All details in:  http://www.idsia.ch/~juergen/oops.html ***/
/******* ** Original code http://www.idsia.ch/~juergen/oopscode.c **/
/** This program  is free software - you can redistribute it and / */
/*** or modify it under the terms of the GNU General Public License*/
/**** as published by the  Free Software Foundation; either version*/
/** 2 of the License, or (at your option) any  later version. ******/
/******* The code is distributed in the hope that it will be useful*/
/*** but WITHOUT ANY WARRANTY; without even the implied warranty ***/
/**** of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. ******/
/******* See the GNU General  Public License for all details. ******/
/** This code layout is  an instance of "crystalline formatting". **/
/**** J. Schmidhuber's philosophy behind crystalline formatting is:*/
/** Some programmers prefer to debug code that looks nice. *********/

/* Goal: First solve symmetry tasks, then Hanoi task - this took 4 */
/** days on the slow 600mhz computer used by Juergen back in 2002 **/
#include            <stddef.h>	/*names starting by an a denote */
#include            <stdlib.h>	/*addresses amin ..-1,0,1..amax */
#include            <math.h>	/*waste q[0](1st element of the */
#include            <stdio.h>	/*array q[]),and start at q[1]! */
#include            <time.h>	/*Optimal search for code saved */
#include            <string.h>	/*in q[]; solves >=1 tasks; may */
/*build on solutions for older tasks frozen in q[] - may metasearch*/
/*Codes grow when an instruction ptr points beyond Q on top; new Q;*/
/*keeps track of all due changes and undoes for next alternative Q!*/

/****** ************ *************** GENERAL MACROS, AND DATA TYPES*/
#define TRUE         1		/*boolean values small integers */
#define FALSE        0
#define maxtask      30		/*simultaneously do <= 30 tasks */
#define amax         10000	/*codes: <= amax q[.]-addresses */
#define amin        -3000	/*amin to 0 hold tape's state s */
#define tapesize    (- amin)	/*all tasks have separate tapes */
#define maxQ         1000	/*max. number of initial tokens */
#define maxfn        100	/*max. self-made function name! */
#define maxpat       10		/*max. self-made search pattern */
#define maxv         100	/*array name may not exceed 100 */
#define maxdata      800	/*num tape cells for the arrays */
#define maxcp        300	/*maxim stackptr of call stacks */
#define maxdp        200	/*maxim stackptr of data stacks */
#define stacksize    6000000	/*one big global stack restores */
#define lolo         long long	/*large integers for time spans */
#define maxint       1000000000	/*tape cell cont can not exceed */
#define minint      -1000000000	/*maxint or fall beneath minint */
#define maxlolo      1000000000000000000L	/*highest possible value */

typedef short BOOL;
typedef void(*FN) ();
typedef void(*FN1) (long);
typedef BOOL(*BOFN) ();
struct INFOQ
{
	FN fn;			/*fn is pointing to C-function! */
	long start;			/*start position of declared Q */
	char *name;
};				/*we can declare named programs */
struct CHAINS
{
	long next;			/*all (un)solved tasks in lists */
	long prev;
};				/*with pointers: back and forth */
struct INFOOLD
{
	long size;			/*size of frozen previous code */
	long start;
};				/*start address of the program */
struct CHANGE
{
	long cell;			/*a tape address - got modified */
	long cont;			/*old content is to be restored */
	long task;
};				/*task number of modified tape */
struct OP
{
	long Q;			/*an instruction number or Qnum */
	long Sp;			/*to reset tapes like before Q */
	long last;			/*solved tasks - before Q's use */
	long SQ;			/*some Qs have a searchQ number */
	lolo t;			/*time: before Q got used first */
	double p;			/*probability of Q given a tape */
	double P;
};				/*probability of Qs before my Q */
				/*last points to a list; Sp into big stack with */
				/*changes due to Q - to reinsert tasks & reset */
				/*t and P needed to test whether runtime <= T*P */

				/****** ************ *************** ***** IMPORTANT TAPE ADDRESSES*/
long acp,			/*cell of task's callstackptr to call functions */
aendcalls,			/*ending of call stack beginning after this acp */
adp,				/*address: local stackpointer is for push & pop */
aendstack,			/*ends arguments stack beginning after this adp */
aDp,				/*address of the second stackptr for pushD etc. */
aendDs,			/*end of the 2nd stack beginning after this aDp */
afnp,				/*number of self-made programs & call addresses */
aendfns,			/*end of list of codes beginning after the afnp */
avp,				/*number of self-generated names of vectors etc */
aendvs,			/*name has size, address - first after this avp */
aendvecs,			/*1st vect after aendvs and more until aendvecs */
atask,			/*the address to hold the tape's problem number */
aquoteflag,			/*if quoteflag=1 then don't exec code but push! */
apatp,			/*topmost search pattern with SQ probabilities! */
acurp,			/*pointer to the distribution of current search */
aendpats,			/*nSQs +2 values per pattern:1st after my acurp */
aenv,				/*environments! */
awork,			/*holds start of modifiable work tape addresses */
aendwork;			/*work tape end */

					/*****  ************ *************** ******** GLOBAL VARIABLES *****/
struct OP q[amax + 1];		/*goal: programs in the q-stack */
struct INFOQ Q[maxQ + 1];	/*for info about an instruction */
struct INFOOLD old[amax + 1];	/*for info about frozen progrms */
struct CHAINS list[maxtask + 1];	/*unsolved tasks & solved tasks */
struct CHANGE S[stacksize + 1];	/*1 global stack restores tapes */
double P;			/*probability of program so far */
lolo t,				/*steps consumed by current prg */
T,				/*time limit for current search */
totalt,			/*total time for search, so far */
topt = 0,			/*longest run of any prg so far */
insts = 0,			/*counting token-instructions * */
prefs = 0;			/*counts: tested prog prefixes */
BOOL mark[maxtask + 1][tapesize + 1],	/*address pushed after last Q * */
halt,				/*normally after semantic error */
jumped,			/*was there jump to an address? */
pushenabled,			/*push a change? yes or no flag */
done,				/*entire problem list is solved */
good;				/*final task not only better but truly finished */
BOFN successfn;			/*variable, task-specific fn for the evaluation */
FN1 inittaskfn;			/*variable, task-specific fn for initialization */
FN1 probfn;			/*variable, task-specific fn for initial probs */

long tape[maxtask + 1][tapesize + 1],	/*dynamical data on task's tape */
SQ[maxQ + 1],			/*compose search-Qs with search */
oldp,				/*old  [oldp] is info about  top frozen program */
ndecl,			/*number of user-defined, decl'd programs in q! */
task,				/*current task & entrance to the unsolved chain */
Sp,				/*pointer to the top stack entry in global stck */
topSp = 0,			/*max. stack ptr seen up to now */
nQs,				/*counts initial prewired codes */
quotenum,			/*number for the token "quote"! */
qp,				/*the pointer to topmost inst in stack-like q[] */
afrozen,			/*older programs unmodifiable up to the afrozen */
nSQs,				/* num of search progs - combine during search! */
acurrent,			/*current tasks: instruction ptr starting here! */
alast,			/*every previous task's solvable from the alast */
toptask,			/*number for top task during the current search */
unsolved,			/*current number of now unsolved problems/tasks */
anchor;			/*start of chain of solved tasks in task list[] */

				/*** ***** TRACK NON-OP TAPE CHANGES IN GLOBAL STACK:POP/PUSH CELLS*/
				/*** 1 big stack for all my parallel tasks; Sp=0 --> stack is empty*/
				/*** pushcells store task's tapecell values before a test of next Q*/
#define stop   {halt  =   TRUE; return  ;}	/*use so frequently! */
#define stop0  {halt  =   TRUE; return 0;}
void
pushcell(long cell)
{
	if (Sp >= stacksize)
	{
		printf("\nStack overflow");
		stop
	}
	if (mark[task][cell])
		return;			/*cell was no virgin! */
	Sp++;				/*else push virgin! */
	S[Sp].cell = cell;
	S[Sp].task = task;
	S[Sp].cont = tape[task][cell];
	mark[task][cell] = TRUE;
}				/*mark it as modified */

void
popcells(long ptr)
{				/*restore all those tapes down to my ptr */
	while (Sp > ptr)
	{
		tape[S[Sp].task][S[Sp].cell] = S[Sp].cont;
		Sp--;
	}
}

void
unmark(long ptr)
{
	long pp = Sp;			/*zero marks down to my ptr */
	while (pp > ptr)
	{
		mark[S[pp].task][S[pp].cell] = FALSE;
		pp--;
	}
}

/*** *************** BASIC FUNCTIONS FOR CALCULATING ON TASK TAPES */
/*** c(a):content of non-q[] address a (given task); z(a): of any a*/
/* a callstack frame holds C(1)= ip; C(2) = base dp; out = num rets*/
/* C(4..n) useful as local variables above top frame of a callstack*/
/*** push & pop: for params / return values: call by value / by ref*/
/*we will not access any nonexisting code beyond qp, or cells <amin*/
BOOL
bad(long a)
{
	return (a < amin || a > qp);
}

#define inct    totalt++;  t++;	/*increment time and total time */
#define tncheck if (n<0 || t+n> T*P)     stop   t+=n; totalt+=n;
#define dp      tape[task]      [-adp]
#define cp      tape[task]      [-acp]
#define ip      tape[task]      [-acp -1 -tape[ task][- acp]]
#define base    tape[task]      [-acp -2 -tape[ task][- acp]]
#define out     tape[task]      [-acp -3 -tape[ task][- acp]]
#define Dp      tape[task]      [-aDp]
#define vp      tape[task]      [-avp]
#define fnp     tape[task]      [-afnp]
#define patp    tape[task]      [-apatp]
#define curp    tape[task]      [-acurp]
long
c(long a)
{
	return tape[task][-a];
}

long
z(long a)
{
	if (a <= 0)
		return tape[task][-a];
	/*then a in s[]; else a in q[] */ return q[a].Q;
}

void
set(long a, long val)
{				/*sets non-q[]-a below address1 */
	a = -a;
	if (tape[task][a] == val)
		return;
	if (pushenabled)
		pushcell(a);		/*only changes! */
	tape[task][a] = val;
}				/*no checks of a and val, trust */

void
cpabn(long a, long b, long n, long min, long max)
{
	if (n < 0 || bad(a) || bad(a + n) || b < min || b + n > max)
		stop if (a == b)
		return;
	tncheck if (b < a)
		while (n > 0)
		{
			set(b, z(a));
			n--;
			b++;
			a++;
		}
	else
	{
		a += n - 1;
		b += n - 1;
		while (n > 0)
		{
			set(b, z(a));
			n--;
			b--;
			a--;
		}
	}
}

/*copy n symbols from  a to b if within time and bounds min,max */
/*consider multi-tasking: a task with n-step-Q's might eat much */
/*more time than others, but all must end; order is irrelevant! */

void
push(long x)
{
	long y = dp + 1;
	if (y > maxdp || minint > x || maxint < x)
		stop set(adp, y);
	set(adp + y, x);
}

long
pop()
{
	long tmp = dp;
	if (tmp == 0)
		stop0 set(adp, tmp - 1);
	return c(adp + tmp);
}

long
top()
{
	long x = dp;
	if (x == 0)
		stop0 return c(adp + x);
}

long
ds(long n)
{
	if (n < 0 || n > maxdp)
		stop0 return c(adp + n);
}				/*nth in stack! */

void
down(long n, long a)
{
	long i = dp - n + 1;		/*cp n down, onto a */
	if (i == a)
		return;			/*already done! */
	if (a > i)
		stop set(adp, a + n);	/*make a new dp */
	a += adp + 1;
	i += adp;			/*a & i: are now true addresses */
	tncheck while (n > 0)
	{
		set(a, c(i));
		n--;
		i++;
		a++;
	}
}

/*we create: another stack @ aDp+1 & its ops pushD & popD and so on*/
void
pushD(long x)
{
	if (Dp == maxdp || x < minint || maxint < x)
		stop set(aDp, Dp + 1);
	set(aDp + Dp, x);
}

long
popD()
{
	long tmp = Dp;
	if (tmp == 0)
		stop0 set(aDp, tmp - 1);
	return c(aDp + tmp);
}

long
topD()
{
	long x = Dp;
	if (x == 0)
		stop0 return c(aDp + x);
}

long
C(long a)
{
	return tape[task][-acp - a - cp];
}

void
setC(long a, long val)		/*set local vars in a top frame */
{
	if (maxint < val || val < minint)
		stop			/*out of bounds */
		set(acp + cp + a, val);
}				/*address of param on stack */

void
pushblock(long m, long n)
{
	long i = cp, a = base,	/*C(2)! */
		j = dp;
	if (m > j)
		stop i += 3;
	if (i + 3 > maxcp)
		stop set(acp, i);		/*now call stack pointer beneath the new frame! */
	if (m < 0)
		setC(2, a);
	else
		setC(2, j - m);
	/*new is oldbase:ALL are params! Or base below m params @ stack */
	setC(3, n);			/*number of call return values! */
	jumped = TRUE;
}				/*jumped as each call varies ip */

void
calla(long m, long n, long a)
{
	pushblock(m, n);
	setC(1, a);
}

/*ip= a; m in; n out;m<0:all in; if n<0 ret all */
void
ret()
{
	long i = cp, n = out;
	if (i < 1)
		stop			/*pop? no frame */
		if (n > dp)
			stop			/*cannot restore as many as I requested */
			if (n >= 0)
				down(n, base);		/*return values: replace inputs */
	set(acp, i - 3);
}				/*resets cp, ip; onestep: ip++! */

				/*** *************** BASIC PRIMITIVE INSTRUCTIONS OF THE SEARCHER **/
				/* Q pops arguments, calculates some expression, and pushes result */
				/*** our macros make C-codes such as c1() and c2() & m1() and m2() */
#define w(A)    void            c##A()         {push (A  );}   \
                     void            m##A()         {push ( -A);}
w(1) w(2) w(3) w(4) w(5) w(6) w(7) w(8) w(9)	/*makes 18 C-functions */
void
and ()
{
	if (pop() && pop())
		push(1);
	else
		push(0);
}

void
or ()
{
	if (pop() || pop())
		push(1);
	else
		push(0);
}

void
not ()
{
	if (pop() <= 0)
		push(1);
	else
		push(0);
}

void
eq()
{
	if (pop() == pop())
		push(1);
	else
		push(0);
}

void
geq()
{
	if (pop() >= pop())
		push(1);
	else
		push(0);
}

void
grt()
{
	if (pop() > pop())
		push(1);
	else
		push(0);
}

void
c0()
{
	push(0);
} void

half()
{
	push(pop() / 2);
}

void
inc()
{
	push(pop() + 1);
} void

dec()
{
	push(pop() - 1);
}

void
add()
{
	push(pop() + pop());
}

void
sub()
{
	long x = pop();
	push(pop() - x);
}				/*jue don't -() */

void
mul()
{
	push(pop() * pop());
} void

by2()
{
	push(pop() * 2);
}

void
divide()
{
	long x = pop();
	if (x == 0)
		stop push(pop() / x);
}

void
remnant()
{
	long x = pop();
	if (x == 0)
		stop push(pop() % x);
}

void
neg()
{
	long x = pop();
	if (x == 0)
		push(1);
	else
		push(-x);
}

void
powr()
{
	long n = pop(), i, m = pop();	/*m>=0, to n-th power */
	if (m <= 1)
	{
		push(1);
		return;
	}
	i = m;			/*instantaneous */
	while (n > 1 && minint < i && i < maxint)
	{
		i *= m;
		n--;
	}
	push(i);
}

void
up()
{
	push(top());
}

void
del()
{
	long x = dp;
	if (x == 0)
		stop set(adp, x - 1);
}

void
clear()
{
	set(adp, 0);
}				/*delete stack! */

void
ex()
{
	long x, m = dp;
	if (m < 2)
		stop x = ds(m);
	set(adp + m, ds(m - 1));
	set(adp + m - 1, x);
}

void
xmn()
{
	long x, m = pop(), n = pop();	/*exchg stack elements */
	m = dp - m + 1;
	n = dp - n + 1;		/*above top entry, too */
	if (m < 1 || m > maxdp || n < 1 || n > maxdp)
		stop x = ds(m);
	set(adp + m, ds(n));
	set(adp + n, x);
}

void
outn()
{
	long n = pop();
	push(ds(dp - n + 1));
}				/*up n! */

void
inn()
{
	long n = pop();
	n = dp - n + 1;		/*down! */
	if (n < 1 || n > maxdp)
		stop set(adp + n, top());
}

void
cpn()
{
	long i, j, n = pop();
	if (n < 0)
		stop i = dp;
	j = i + n;
	if (j > maxdp)
		stop set(adp, j);
	j += adp;
	i += adp;			/*true! */
	tncheck /*copy */ while (n > 0)
	{
		set(j, c(i));
		n--;
		i--;
		j--;
	}
}

void
xmnb()
{
	long x, m = pop(), n = pop();	/*exchg stack elements */
	m = base + m;
	n = base + n;			/*index relative to base ptr C2 */
	if (m < 1 || m > maxdp || n < 1 || n > maxdp)
		stop x = ds(m);
	set(adp + m, ds(n));
	set(adp + n, x);
}

void
outb()
{
	long n = pop();
	push(ds(base + n));
}				/*nth + base */

void
inb()
{
	long n = pop();
	n = base + n;			/*top to base+n */
	if (n < 1 || n > maxdp)
		stop set(adp + n, top());
}

void
cpnb()
{
	long n = pop();		/*copy n on base onto my stack */
	cpabn(adp + base + 1, adp + c(adp) + 1, n, adp + 1, aendstack);
	set(adp, dp + n);
}

void
ip2ds()
{
	push(ip);
} void

pip()
{
	setC(1, pop());
}

void
pushdp()
{
	push(dp + 1);
}				/*add 1 to count this push, too */

void
popdp()
{
	long a = pop();
	if (a < 0 || maxdp < a)
		stop set(adp, a);
}

void
addadp()
{
	push(pop() + adp);
}				/*adds offset of stack's start! */

void
jmp1()
{
	if (pop() > 0)
	{
		setC(1, pop());
		jumped = TRUE;
	}
}

/*ipok: checks & onestep jumps & doesn't do ip++(like in calls) */
/*nonconditional jumps with e.g. pip() don't set jumped to TRUE */
/*if quoteflag is on don't interpret code, just push it in onestep!*/
void
qot()
{
	set(aquoteflag, 1);
}				/*and next quote will reset it! */

void
toD()
{
	pushD(pop());
} void

fromD()
{
	push(topD());
}

void
delD()
{
	long x = Dp;
	if (x == 0)
		stop set(aDp, x - 1);
}

/*** *************** SOME PRIMITIVES FOR DECLARING & CALLING CODES */
/*on each tape: list of all selfmade fns -> pointers to addresses &*/
/* & num return vals & parameters on top of a stack, to be consumed*/
void
exec()
{
	long n = pop();
	if (n < 1 || n > nQs)
		stop(*Q[n].fn) ();
}

/*views n as the name of a token and executes! */
void
def()
{
	long i = 1 + fnp;
	if (i > maxfn)
		stop			/*new fn */
		set(afnp, i);
	i = 3 * i + afnp;		/*make a name:it is last name+1 */
	set(i, ip + 1);
	set(i - 1, pop());
	set(i - 2, pop());
}				/*selfmade fn! */

				/*label= ip+1 ;  num ret values; num parameters; recursion ok! */
void
topf()
{
	push(fnp);
}				/*push the top selfdefined fn */

void
popf()
{
	long i = fnp;
	if (i == 0)
		stop push(i);
	set(afnp, i - 1);
}				/*undefines last function! */

void
dof()
{
	long n = pop();		/*calls selfmade fn by its name */
	if (n < 1 || n > fnp)
		stop			/*no such name! */
		n = afnp + 3 * n;
	pushblock(c(n - 2), c(n - 1));	/*nums ins/outs */
	setC(1, c(n));
}				/*ip= address of a called label */

void
intpf()
{
	long n = fnp;			/* get number of inputs of topf */
	if (n < 1)
		stop /*no such name! */ push(c(afnp + 3 * n - 2));
}				/*num ins */

void
outpf()
{
	long n = fnp;			/* get number of ouputs of topf */
	if (n < 1)
		stop /*no such name! */ push(c(afnp + 3 * n - 1));
}				/*num ins */

void
oldf()
{
	long a = pop();
	if (a < 0 || a > oldp)
		stop			/*bad old */
		pushblock(0, 0);
	setC(1, old[a].start);
}				/*last in last out ok */

				/*juergen better pushbl(-1,-1)? */
void
rt1()
{
	if (0 < pop())
		ret();
}

void
rt0()
{
	if (0 >= pop())
		ret();
}				/*cond. returns */

void
nop()
{
	;
}				/*to structure a program "("")" */

void
stf()
{
	setC(1, pop() + adp);
}				/*sets ip to run code on stack! */

void
basef()
{
	setC(1, base + adp);
}				/*ip = base, run code on stack! */

void
bsjmp()
{
	setC(1, base + adp + pop());
}				/*ip = base + n on ds */

void
bsf()
{
	calla(-1, -1, base + adp + pop() + 1);
}				/*ret later to code! */

				/*** *************** SOME PRIMITIVES TO EDIT CODE ON THE DATA STACK*/
void
getq()
{
	long a = pop(), n;
	if (a < 0 || a > oldp)
		stop			/*bad old */
		n = old[a].size;		/*push 1 frozen, maybe to edit! */
	cpabn(old[a].start, adp + 1 + dp, n, adp + 1, aendstack);
	set(adp, dp + n);
}

void
insq()
{
	long b = pop(), n, a = pop(), m = dp - base - b;
	if (a < 0 || a > oldp || b < 0 || m < 0)
		stop			/*insert frozen */
		n = old[a].size;
	b += adp + base + 1;		/*right above b+ top stack base */
	cpabn(b, b + n, m, adp + 1, aendstack);
	cpabn(old[a].start, b, n, adp + 1, aendstack);
	set(adp, dp + n);
}				/*after base + b insert the q^a */

void
find()
{
	long k = pop(), i = dp;	/*get position of k! */
	while (i > 0 && c(i + adp) != k && t < T * P)
	{
		i--;
		inct
	}
	push(i);
}

void
findb()
{
	long k = pop(), i = base + 1;	/*find pos above base */
	while (c(adp + i) != k && t < T * P)
	{
		i++;
		inct
	}
	push(i);
}

void
deln()
{
	long n = pop(), m = pop();
	if (m < 0 || n < 0)
		stop			/*delete n after stack base + m */
		m += adp + base;		/*m + address of base in stack! */
	cpabn(m + n + 1, m + 1, dp - base - n, adp + 1, aendstack);
	set(adp, dp - n);
}

void
mvn()
{
	long b = pop(), n = pop(), a = pop(), m = base + adp;
	cpabn(m + a, m + b, n, adp + 1, aendstack);
	a = b + n - 1;
	if (a > dp)
		set(adp, a);
}

/*copy n from a  on base C2 to b maybe reset dp */
void
insn()
{
	long b = pop(), n = pop(), a = pop(), m = dp - base - b;
	if (b < 0 || m < 0 || n < 1)
		stop b += adp + base + 1;
	a += adp + base;
	cpabn(b, b + n, m, adp + 1, aendstack);
	cpabn(a, b, n, adp + 1, aendstack);
	set(adp, dp + n);
}				/*insert n: from base+a after+b */

				/*** * BIAS-SHIFTING PRIMITIVES THAT MODIFY THE CODE PROBABILITIES */
				/*on tape: sum & max of unnormalized Q-probabilities of search list*/
				/*to get prob: pn(n) is unnormalized probability for n-th search SQ*/
				/* a selfreferential action modifies probability for search options*/
				/* a search  pattern defines a prob. distribution on possible SQ's!*/
#define poff    acurp + curp * (nSQs+2)	/*probs: offset */
long
psum()
{
	return c(poff + 1);
}

long
pmax()
{
	return c(poff + 2);
}

long
pn(long n)
{
	return c(poff + 2 + n);
}

void
setp(long n, long x)
{
	set(poff + 2 + n, x);
}				/*prob changes: */

void
setmax(long x)
{
	set(poff + 2, x);
}				/*metasearching */

void
setsum(long x)
{
	set(poff + 1, x);
}

long
get2ndmax()
{
	long n = poff + 2, x = pmax(), m = n, s = 0, end = n + nSQs;
	do
	{
		n++;
	} while (c(n) != x);		/*find 2nd-highest <=pmax */
	do
	{
		m++;
		if (s < c(m) && m != n)
			s = c(m);
	}				/*jue tncheck? */
	while (s < x && m < end);
	return s;
}

void
addtoSQ(long i, long val)
{
	long x;			/*increase prob of ith SQ */
	if (val < 1 || i > nSQs || i < 1)
		return;			/*not possible! */
	x = psum() + val;
	if (x > maxint)
		return;			/*has max normalizer */
	setsum(x);			/*normalizer + */
	x = pn(i) + val;
	setp(i, x);
	if (x > pmax())
		setmax(x);
}				/*maximal SQprob has increased */

void
subofSQ(long i, long val)
{
	long x;			/*decrease prob of ith SQ */
	if (val < 1 || i > nSQs || i < 1)
		return;			/*not possible! */
	x = pn(i) - val;
	if (x < 0)
		return;			/*no neg probabilities! */
	setsum(psum() - val);
	setp(i, x);			/*don't check if =0! */
	if (x + val == pmax())
		setmax(get2ndmax());
}				/*change of max */

void
incSQ()
{
	long i = top();
	addtoSQ(i, 1);
}				/*top, not pop! */

void
decSQ()
{
	long i = top(), x, y, z;	/*decrem prob of the SQ */
	if (i > nSQs || i < 1)
		return;			/*no such search Q number known */
	x = pn(i);
	if (x == 0)
		return;			/*SQ: already 0 */
	y = psum();
	z = pmax();
	if (x == 1 && y <= z + 1)
		stop			/*leave at least 2 SQs */
		if (x == z)
			setmax(get2ndmax());	/*change of max */
	setp(i, x - 1);
	setsum(y - 1);
}				/*normalizer -1 */

long upSQ;			/*SQ probability:enumerator  +=  upSQ: increase */
void
oldSQ()
{
	long a = pop() + ndecl, n, i;
	if (a < 0 || a > oldp)
		stop			/*bad */
		n = old[a].size;
	a = old[a].start;		/*all SQs of old nondecl: +upSQ */
	tncheck n += a;
	for (i = a; i < n; i++)
		addtoSQ(SQ[q[i].Q], upSQ);
}

void
setpat()
{
	long i = pop();		/*instantiate my search pattern */
	if (i < 0 || i > patp)
		stop			/*no such search pattern exists */
		set(acurp, i);
}				/*next SQ-search defined via new probabilities! */

void
pupat()
{
	long i = apatp;		/*push search pattern */
	if (i > maxpat)
		stop i++;
	set(apatp, i);		/*not too many? */
	cpabn(poff + 1, acurp + 1 + i * (2 + nSQs), 2 + nSQs, acurp + 1, aendpats);
}

void
popat()
{
	long i = apatp;
	if (i == 0)
		stop set(apatp, i - 1);
	push(i);
}				/*pop search pattern */

				/*** *************** *************** PROBLEMSPECIFIC THINGS: HANOI */
				/*** rule: represent each modifiable aspect of world on task tapes!*/
				/*** we are starting at aenv - first top1, then disk 1,2,..., top1;*/
				/*at aenv+maxtask +1 find top2, then disks 1,..top2, and so on...  */
				/*** push on stack:  1=source peg, 2 = aux, 3= dest, then num disks*/
#define hanoff (aenv+(tower-1)* dsize)	/*offset: frequent macro */
long dsize, envsize;
void
initenvpars()
{
	dsize = maxtask + 1;
	envsize = 3 * dsize;
}

long
gettop(long tower)
{
	return c(hanoff);
}

long
getdisk(long tower, long ptr)
{
	return c(hanoff + ptr);
}

void
settop(long tower, long val)
{
	set(hanoff, val);
}

void
setdisk(long tower, long ptr, long val)
{
	set(hanoff + ptr, val);
}

void
inittaskhanoi(long n)
{
	long i;
	task = n;
	set(atask, n);
	settop(1, n);
	settop(2, 0);
	settop(3, 0);
	for (i = 1; i <= n; i++)
	{
		setdisk(1, i, n + 1 - i);
		setdisk(2, i, 0);
		setdisk(3, i, 0);
	}
	clear();
	push(1);
	push(2);
	push(3);
	push(n);
}

void
movdisk(long a, long b)
{
	long topa = gettop(a), topb;
	if (topa == 0)
		stop topb = gettop(b);
	if (topb > 0 && getdisk(b, topb) < getdisk(a, topa))
		stop topb++;
	settop(b, topb);
	setdisk(b, topb, getdisk(a, topa));
	setdisk(a, topa, 0);
	settop(a, topa - 1);
}

void
printhanoi()
{
	long tower, tmp, i;
	printf("\n\nENV:  ");
	for (tower = 1; tower <= 3; tower++)
	{
		tmp = gettop(tower);
		printf("[");
		for (i = 1; i < tmp; i++)
			printf("%d,", getdisk(tower, i));
		printf("%d", getdisk(tower, i));
		printf("]  ");
	}
}

BOOL
successhanoi()
{
	return (c(aenv) == 0 && c(aenv + dsize) == 0);
}

/*pegs 1&2 empty */
void
tsk()
{
	push(c(atask));
}				/* primitive: get task size; */

void
mvdsk()
{
	long a = ds(base + 1), b = ds(base + 3);
	if (a < 1 || a > 3 || b < 1 || b > 3 || a == b)
		stop movdisk(a, b);
}

void
x23()
{
	push(2);
	push(3);
	xmn();
}				/*xch mvdsk par */

void
x34()
{
	push(3);
	push(4);
	xmn();
}

/*** *************** *************** PROBLEMSPECIFIC SYMMETRY ON D */
/*** goal:  given n, push n 1s & 2s, symmetrically @ second D stack*/
void
onetoD()
{
	pushD(1);
} void

twotoD()
{
	pushD(2);
}

void
inittasksymm(long n)
{
	task = n;
	set(atask, n);
	clear();
	push(n);
}

BOOL
successsymm()
{
	long i = aDp + Dp, j = i - task - task;
	if (j <= aDp)
		return FALSE;
	j += task;			/*jue c(i) too slow: */
	while (i > j && tape[task][-i] == 2)
		i--;			/*success if on */
	if (i != j)
		return FALSE;
	j -= task;			/*D: n 1s, n 2s */
	while (i > j && tape[task][-i] == 1)
		i--;			/*assumes it is */
	if (i == j)
		return TRUE;
	return FALSE;
}				/*instantaneous */

				/*alternatively: measure time by counting tape's checked cells! */

				/******************* ENTER PRIMITIVE INSTRUCTIONS  & COMPLEX PROGS */
				/*we will now create initial perhaps recursive codes that go to q[]*/
				/*enter(A) to assign code & Qnum and 0 start-address to Q's name, A*/
				/*enterv and enterw: enter code such as in5(),x34(), cp3() & C4C2()*/
				/*ENTER (foo) states that foo is one of the codes in optimal search*/
				/*decl(m,n,foo,body) makes footext & fooaddress; foo code: m inputs*/
				/*n outputs; at most 1 new name in a body, for 1fold crossrecursion*/
				/*also makes gtfoo() to push code of foo onto stack, to edit it etc*/
				/*enterq(foo): inits foo's address = topq+1 (to old);enter;body>q[]*/

#define         enter(A)        nQs++;          Q[nQs].fn=(*A);\
                     Q[nQs].name=#A;                 Q[nQs].start=0;
#define         ENTER(A) nSQs++;SQ[nSQs]      = Qnum(#A);
#define         decl(M,N,A,B)   char            A##text[]= #B; \
                     long            A##address,     A##size;       \
	             void(A)()      {calla(M,N,      A##address);}
#define         enterq(A)       A##address    = qp+1;   enter(A)\
                     oldp++;ndecl++; alast         = old[oldp].start=\
                     Q[Qnum(#A)].    start = qp+1;   writeq(A##text);\
                     A##size=old[oldp].size= qp- old[oldp].start + 1;

long
Qnum(char name[])
{
	long i = 1;			/*name to Qnum! */
	while (i <= nQs && strcmp(name, Q[i].name))
		i++;
	if (i > nQs)
	{
		printf("NEW:");
		printf(name);
		printf("\n");
	}
	return i;
}

long
SQnum(char name[])
{
	long i = 1, n = Qnum(name);
	while (i <= nSQs && n != SQ[i])
		i++;
	if (i > nSQs)
	{
		i = 0;
		printf("NEW SQ!");
	}
	return i;
}

void
writeq(char s[])
{
	char *p = strtok(s, " ");
	while (p != 0)
	{
		qp++;
		q[qp].Q = Qnum(p);
		q[qp].p = 1.0;
		q[qp].P = 1.0;
		p = strtok(0, " ");
	}
}

/*eg char foo[]="c3 up mul cp3"; writeq (foo) to write foo>>q[] */

/*to decide which of your C-programs to use to build complex tokens*/
void
initsimple()
{
	nQs = 0;
	enter(onetoD) enter(twotoD)
		enter(mvdsk) enter(x23) enter(x34)
		enter(bsf) enter(oldSQ)
		enter(add) enter(mul) enter(powr) enter(sub)
		enter(divide) enter(inc) enter(dec) enter(by2)
		enter(getq) enter(insq) enter(findb)
		enter(incSQ) enter(decSQ) enter(pupat) enter(setpat)
		enter(insn) enter(mvn) enter(deln) enter(intpf)
		enter(def) enter(topf) enter(dof) enter(oldf)
		enter(bsjmp) enter(ret) enter(rt0)
		enter(neg) enter(eq) enter(grt) enter(clear)
		enter(del) enter(up) enter(ex) enter(jmp1)
		enter(outn) enter(inn) enter(cpn) enter(xmn)
		enter(outb) enter(inb) enter(cpnb) enter(xmnb)
		enter(ip2ds) enter(pip) enter(pushdp) enter(popdp)
		enter(toD) enter(fromD) enter(delD) enter(tsk)
		enter(c0) enter(c1) enter(c2)
		enter(c3) enter(c4) enter(c5) enter(exec)
		enter(qot) enter(nop) quotenum = Qnum("qot");
}

/*now we declare a few programs, thus illustrate possibilities: */
/*c999: computes const:  nothing in, 1 out (999) on stack's top */
/*simple testexp pops x & y from stack & pushes [6x (4y - 1)]^2 */
/*then recursive fak(n):pop n;if 0 return 1 else n * fak(n - 1) */
/*and fak2: make selfdefined fak function, whose name is 1; run */
/*tailrec(x,fn11)returns x if n (on base)=0 else recurs(n-1,fn) */
/*defnp, calltp, endnp recursion scheme for proc with ret if n=0 */

decl(0, 1, c999, c4 c5 powr c5 c5 mul sub ret) decl(2, 1, testexp, c4 mul dec c3 c2 mul mul mul up mul ret) decl(1, 1, fak, up c1 ex rt0 del up dec fak mul ret) decl(1, 1, fak2, c1 c1 def up c1 ex rt0 del up dec topf dof mul ret) decl(-1, -1, defnp, c0 toD pushdp dec toD qot def up rt0 dec intpf cpn qot ret)	/*num pars on Dstack, quote begin of defproc */
decl(-1, -1, calltp, qot topf dof intpf cpn qot ret)	/*`call top proc' */
decl(-1, -1, endnp, qot ret qot fromD cpnb fromD up delD fromD ex bsf ret)
/*`ret'; call fn def with number of pars found @ Ds... bsjmp also ok: */
decl(-1, -1, tailrec, qot c1 c1 def up qot c2 outb qot ex rt0 del up dec topf dof qot c3 outb qot ret qot c1 outb c3 bsjmp)	/*no bsf:rt0 */
																															/*to decide which of numerous decl'd programs really go to q[]stack*/
	void initdecl()
{
	qp = 0;
	oldp = 0;
	alast = 0;
	ndecl = 0;
	enterq(fak) enterq(fak2) enterq(c999) enterq(testexp)
		enterq(defnp) enterq(calltp) enterq(endnp) afrozen = qp;
}

/*to decide which of many primitives && declarations will become my*/
void
initSQ()
{
	nSQs = 0;			/*basic programs for the search */
	ENTER(c2) ENTER(c3) ENTER(mul) ENTER(getq) ENTER(bsjmp)
}

void
initSQall()
{
	long i;
	for (i = 1; i <= nQs; i++)
		SQ[i] = i;
	nSQs = nQs;
}

/*** *************** *************** ***** REMAINING INITIALIZATION*/
void
initaddresses()
{				/*first: initSQ, & initenvpars! */
	acp = amin;
	aendcalls = acp + maxcp;
	adp = aendcalls + 1;
	aendstack = adp + maxdp;
	aDp = aendstack + 1;
	aendDs = aDp + maxdp;
	afnp = aendDs + 1;
	aendfns = afnp + 3 * maxfn;
	avp = aendfns + 1;
	aendvs = avp + 2 * maxv;
	aendvecs = aendvs + maxdata;
	atask = aendvecs + 1;
	apatp = atask + 1;
	acurp = apatp + 1;
	aendpats = acurp + (maxpat + 1) * (nSQs + 2);	/*2 for sum&max */
	aquoteflag = aendpats + 1;
	aenv = aquoteflag + 1;
	awork = aenv + envsize;
	aendwork = 0;
}

/*** macros to boost or weaken init. probability  of a search token*/
#define         boost(A)        addtoSQ(SQnum  (#A),    upSQ);
#define         weaken(A)       subofSQ(SQnum  (#A),    upSQ);
void
initmaxent()
{
	long i;
	set(apatp, 0);
	set(acurp, 0);		/*0=only initial search pattern */
	setsum(nSQs);
	setmax(1);			/*initialize all by max entropy */
	for (i = 1; i <= nSQs; i++)
		setp(i, 1);
}

void
probsymm(long n)
{
	task = n;
	initmaxent();
	boost(c1) boost(c2) boost(dec) boost(by2) boost(oldSQ)
}

void
probhanoi(long n)
{
	task = n;
	initmaxent();
	boost(c3) boost(c4) boost(c5) boost(dec) boost(by2) boost(oldSQ)
}

void
inittapes()
{
	long j;
	for (task = 1; task <= maxtask; task++)
	{
		for (j = 0; j <= tapesize; j++)
		{
			mark[task][j] = FALSE;
			tape[task][j] = 0;
		};
	}
}

void
inittasks()
{
	long i;			/*get open chain with all tasks */
	anchor = 0;			/*starts list of solved tasks  */
	for (i = 1; i <= maxtask; i++)
	{
		list[i].next = i - 1;
		list[i].prev = i + 1;
		(*inittaskfn) (i);
		(*probfn) (i);
		printhanoi();
	}
}

void
initbasics()
{
	pushenabled = FALSE;
	initsimple();
	initdecl();
	initSQall();
	upSQ = nSQs;
	initenvpars();
	initaddresses();
	inittapes();
	inittasks();
	q[afrozen].Sp = 0;
	Sp = 0;
	totalt = 0;
	alast = afrozen + 1;
	pushenabled = TRUE;
}

/*** *************** *************** *************** OUTPUT ********/
#define  pr(A)  printf("\n");   printf(#A);     printf(":%d",A);
#define  prlolo(A)  printf(#A); printf(":"); printlolo(A);printf("\t");
#define  prc(A) printf("\n\n"); printf(#A);     printf(":%d ",c(a##A));
void
printlolo(lolo k)
{
	long i, j;			/*for long long ints */
	if (k <= 1000000000)
	{
		i = k;
		printf("%d", i);
	}
	else
	{
		j = k / 1000000000;
		i = k % 1000000000;
		printf("%d%09d", j, i);
	}
}

void
printmarks()
{
	long i;
	printf("\nMARKS:");
	for (i = 0; i <= tapesize; i++)
		printf("%d ", mark[task][i]);
}

void
printQ(long i)
{
	printf("[%d:%d ", i, q[i].Q);
	printf(Q[q[i].Q].name);
	if (q[i].p < 1.0)
		printf(" %4.3f", q[i].p);
	if (q[i].P < 1.0)
		printf(" %4.7f", q[i].P);
	printf("]");
}

void
printold(long n)
{
	long i, j;
	printf("\n%d: ", n);
	j = old[n].start + old[n].size - 1;
	for (i = old[n].start; i <= j; i++)
		printQ(i);
	printf("\n\n");
}

void
printolds()
{
	long i;
	printf("\nOLD PROGRAMS:\n");
	for (i = 1; i <= oldp; i++)
		printold(i);
	printf("\nNOT OLD YET:\n");
	for (i = old[oldp].start + old[oldp].size; i <= qp; i++)
		printQ(i);
}

void
printq()
{
	long i;
	printf("\nq: ");
	for (i = 1; i <= qp; i++)
		printQ(i);
}

void
printSQ()
{
	long i;
	printf("\n\nSEARCHQS:");
	for (i = 1; i <= nSQs; i++)
	{
		printf("[%d:%d ", i, SQ[i]);
		printf(Q[SQ[i]].name);
		printf("]  ");
	}
}

void
printblock(long a)
{
	long k;
	printf("%d:", a - acp);
	printf("[ip %d ", c(++a));
	printf("dp %d ", c(++a));
	printf("out %d", c(++a));
	printf("]  ");
}

void
printpat(long n)
{
	long i, a = acurp + n * (nSQs + 2);
	printf("\n%d:", n);
	printf("[%d ", c(a + 1));
	printf("max %d ", c(a + 2));
	printf("probs: ");
	for (i = 1; nSQs >= i; i++)
		printf("%d ", c(a + 2 + i));
	printf("]  ");
}

void
printtape()
{
	long i;
	printf("\n\n-TAPE:");
	prc(cp) printf("calls:");
	for (i = acp; i < acp + maxcp; i += 3)
		printblock(i);
	prc(dp) printf("data stack:");
	for (i = adp + 1; i <= aendstack; i++)
		printf("%d:%d ", i - adp, c(i));
	prc(Dp) printf("2nd data stack:");
	for (i = aDp + 1; i <= aendDs; i++)
		printf("%d:%d ", i - aDp, c(i));
	prc(fnp) printf("fns:");
	for (i = afnp + 1; i <= aendfns; i += 3)
		printf("%d:(%d,%d,%d) ", (i - afnp) / 3 + 1, c(i), c(i + 1),
			c(i + 2));
	prc(vp) printf("vs:");
	for (i = avp + 1; i <= aendvs; i += 2)
		printf("(%d,%d) ", c(i), c(i + 1));
	printf("data:");
	for (i = aendvs + 1; i <= aendvecs; i++)
		printf("%d ", c(i));
	prc(task) prc(patp) prc(curp) for (i = 0; maxpat >= i; i++)
		printpat(i);
	prc(quoteflag) printf("\n\nenv: ");
	for (i = aenv; i < awork; i++)
		printf("%d ", c(i));
	printf("\n\nwork:");
	for (i = awork; i <= aendwork; i++)
		printf("%d ", c(i));
}

void
printstack()
{
	long i;
	printf("\n\nSTACK> ");
	for (i = 1; i <= Sp; i++)
		printf("(%d:%d %d)  ", S[i].task, S[i].cell, S[i].cont);
}

void
printchains()
{
	long i, tmp;
	printf("\n\nSOLVED:");
	i = anchor;
	while (i != 0)
	{
		printf("%d,", i);
		i = list[i].prev;
	}
	printf("UNSOLVED:");
	if (!unsolved)
		return;
	i = tmp = list[task].next;
	do
	{
		printf("%d,", i);
		i = list[i].next;
	}
		/*tmp ok even if task solved */ while (i != tmp);
}

void
show()
{
	printf("\n\n------------ SHOW START ----------------\n");
	printolds();
	printSQ();
	printhanoi();
	printtape();
	printchains();
	printstack();
	printf("\n\n");
	prlolo(T);
	prlolo(prefs);
	prlolo(insts);
	prlolo(totalt);
	prlolo(topt);
	pr(topSp);
	pr(afrozen);
	pr(alast);
	pr(acurrent);
	printf("\n\n------------ SHOW END ------------------\n");
}

/*** *************** MULTITASKING TO RUN CODES - BUT DO NOT SEARCH */
/*** 1 task per tape - keep circling among nonsolved problems until*/
/*** ip meets search address at qp+1 or halt or time limit used up!*/

void
removetask()
{
	unsolved--;			/*remove current task from list */
	list[list[task].prev].next = list[task].next;
	list[list[task].next].prev = list[task].prev;
	list[task].prev = anchor;
	anchor = task;
}				/*task.next unchanged */

void
reinserttask()
{
	unsolved++;			/*anchor!=0;undo recent removal */
	task = anchor;		/*task.next unchanged */
	anchor = list[task].prev;
	list[task].prev = list[list[task].next].prev;
	list[list[task].next].prev = task;
	list[list[task].prev].next = task;
}				/*ok when unsolved empty */

void
dummy()
{
	;
}

void
onestep()
{
	long n = z(ip);		/*execute single Q--instruction */
	if (t > 2 * topt)
	{
		topt = t;			/*show(); */
	}
	if (Sp > 2 * topSp)
	{
		topSp = Sp;		/*show(); */
	}				/*snapshot pics */
	jumped = FALSE;
	insts++;
	inct				/*some Q's cost more! */
		if (1 == c(aquoteflag))
			if (n == quotenum)
				set(aquoteflag, 0);
			else
				push(n);			/*if quote, then just push it!! */
		else
			(*Q[n].fn) ();		/*calls function of the Q at ip */
	if (!jumped)
		setC(1, ip + 1);		/*increments ip */
	if ((*successfn) ())
		removetask();		/*jue: if halt? */
	task = list[task].next;
}				/*ok - even when task removed!! */

BOOL
ipok()
{
	long a = ip;			/*is ip  valid? */
	if (a < amin || a > qp)
		return FALSE;
	if (z(a) < 1 || z(a) > nQs)
		return FALSE;
	return TRUE;
}

void
stepuntil()
{				/*til all solved or halt or time out or search! */
	halt = FALSE;
	while (unsolved && ipok() && (!halt) && t + unsolved <= T * P)
		onestep();
}

/*** *************** ********* TRACK OP CHANGES:PUSH,POP,BACKTRACK */
/*** different tapes carry different probabilities & search options*/
/*** but that is all right: every SQ search uses one tape/task that*/
/*** defines allowed alternatives on all tapes - 1st request winner*/
void
maybepushQ()
{				/*exclusively at peculiar search address qp + 1 */
	if (halt || ip != qp + 1)
		return;			/*wrong address */
	if (T * P * pmax() < (t + unsolved) * psum())
		return;			/*lack of time! */
	if (qp >= amax)
	{
		printf("\n CODE CRASH");
		return;
	}
	unmark(q[qp].Sp);		/*all marks to 0,init with zero */
	++qp;
	q[qp].last = anchor;		/*last  solution before this Q! */
	q[qp].Sp = Sp;		/*restore tapes: pop down here! */
	q[qp].SQ = 0;			/*first SQ for search will come in nextQ! */
	q[qp].t = t;
	q[qp].P = P;
}

void
restoretasks(long below)
{
	while (anchor != below)
		reinserttask();
}

void
restoreQ()
{				/*reset all like before use of top's Q */
	unmark(q[qp].Sp);		/*set marks to 0 after Q's test */
	popcells(q[qp].Sp);		/*restores tapes like before Q! */
	restoretasks(q[qp].last);	/*reinsert tasks solved with Q! */
	t = q[qp].t;			/*make t, P like after 1st push */
	P = q[qp].P;
}

BOOL
nextQ()
{
	long i = q[qp].SQ, sum;
	double tmp;
	if (i != 0)
		restoreQ();		/*if this SQ not freshly pushed */
	if (i == nSQs)
		return (FALSE);		/*if last search Q, no next SQ! */
	sum = psum();
	tmp = T * P / (sum * (t + unsolved));	/*restored prob */
	do
	{
		i++;
	} while (i <= nSQs && tmp * pn(i) < 1.0);	/*enough time? */
	if (i > nSQs)
		return (FALSE);		/*no alternative left for my qp */
	/*else: */ q[qp].SQ = i;
	/*next SQ is ok, sufficient prb */
	q[qp].Q = SQ[i];		/*Qnum from SQ! */
	q[qp].p = (double)pn(i) / sum;
	P = q[qp].P * q[qp].p;
	prefs++;
	return (TRUE);
}				/*divide prob by the normalizer */

void
backtrack()
{
	while (qp > afrozen && (!nextQ()))
		qp--;
}

/*** *************** *************** PROBLEM SOLVING AND SEARCHING */
void
search()
{				/*simultaneously solve all tasks in a task ring */
	t = 0;
	P = 1.0;			/*now do forever (until exitus) */
	for (;;)
	{
		stepuntil();		/*done?  new Q?  halt?   t/P>T? */
		if (unsolved == 0)
		{
			done = TRUE;
			return;
		}			/*done */
		maybepushQ();		/*push, if new Q request & time */
		backtrack();		/*next Q chosen, or no SQs left */
		if (qp == afrozen)
			return;
	}
}				/*was not successful */

void
reset()
{				/*reset all tapes/marks for all tasks - but leave q[]! */
	unmark(0);
	popcells(0);
	restoretasks(0);
}

void
searchring(long n, long m)
{				/*task m>task n */
	unsolved = m - n + 1;		/*num of chain's unsolved tasks */
	if (unsolved > T)
		return;			/*lacks the time to initialize! */
	list[m].prev = n;		/*close a chain: m, m-1, ..., n */
	list[n].next = m;
	pushenabled = FALSE;		/*set initial ip's, do not push */
	for (task = n; task <= m; task++)
		setC(1, acurrent);
	pushenabled = TRUE;		/*1st ip of main call is at my acurrent */
	task = m;			/*start with top task in a ring */
	search();
	if (unsolved == 0)
	{
		printf("\n\n ALL SOLVED! ");
		show();
	}
	reset();			/*totally resets tapes & marks & unsolved tasks */
	list[n].next = n - 1;		/*reopens ring! */
	list[m].prev = m + 1;
}

void
solveupto(long n)
{				/*(tasks,ip)=(n, alast), or (1-n,afrozen+1) */
	qp = afrozen;
	T = 1;
	done = FALSE;			/*forever loop: */
	for (;;)
	{
		printf("\n");
		prlolo(T);
		prlolo(insts);
		prlolo(prefs);
		prlolo(totalt);
		acurrent = alast;		/*known: solves tasks<n */
		searchring(n, n);	/*solve only n! */
		if (done)
			return;			/*exit for-loop */
		acurrent = afrozen + 1;	/*1st un-frozen */
		searchring(1, n);	/*each up to n! */
		if (done)
			return;			/*exit for-loop */
		if (T >= maxlolo / 2)
		{
			printf("\n\nT: CRASH");
			return;
		}
		T *= 2;
	}
}

/*jue redundant: 1st alast above afrozen anyway */

void
freeze()
{				/*from acurrent: 1 - n solvable; keep newer Q's */
	afrozen = qp;			/*maybe new top frozen addr,alast>0 surely */
	if (alast != acurrent)
	{
		oldp++;
		old[oldp].start = alast;
		old[oldp].size = acurrent - alast;
	}
	alast = acurrent;		/*is always ok! */
	q[afrozen].Sp = 0;
}				/*unmark in next 1st pushQ: goes down here */

void
run()
{
	long i;
	for (i = 1; maxtask >= i; i++)
	{
		solveupto(i);
		freeze();
	}
}

void
test()
{
	inittaskfn = (*inittasksymm);
	successfn = (*successsymm);
	probfn = (*probsymm);
	initbasics();
	run();
	inittaskfn = (*inittaskhanoi);
	successfn = (*successhanoi);
	probfn = (*probhanoi);
	pushenabled = FALSE;
	inittasks();
	pushenabled = TRUE;
	run();
}

/*** *************** *************** *************** MAIN **********/
/*** macros for test of declarations by user:testexp(10,5), fak(12)*/
#define open(A)(){long a,n=7;   inittaskfn =   (* inittaskhanoi);\
     initbasics();   unsolved=1;     successfn =    (* successhanoi); \
     task=n; list   [task].next=n;   list[task].     prev=n;t=0;      \
     T=10000;        P=1.0;          a = Q[Qnum(#A)].start;
#define openD(A)(){long a,n=7;  inittaskfn =   (* inittasksymm); \
     initbasics();   unsolved=1;     successfn =    (* successsymm);  \
     task=n; list   [task].next=n;   list[task].     prev=n;t=0;      \
     T=10000;        P=1.0;          a = Q[Qnum(#A)].start;
#define close   setC(1,a);      stepuntil();    show();        }

void test1
open(testexp)
push(10);
push(5);
close void test2 open(fak2) clear();
push(12);
close int main()
{
	test();
}
