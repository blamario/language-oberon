MODULE AGRS;
(*
      Modul AGRS - Attributed Graph Rewriting System

      Najnizi modul. Ovde su implementirani 
      apstraktni tipovi podataka (ADT) koji cine graf izraza.
*)

CONST
   MaxStack= 6495;
   Fixed*= MAX(INTEGER);
   Unique*= 0;
TYPE
   Term*= POINTER TO TermDesc;            (* ADT Term - korenska klasa *)

   TermDesc*= RECORD
      indirection-: Term;
   END;

   SubTerm*= POINTER TO SubTermDesc;      (* ADT SubTerm *)
   SubTermDesc*= RECORD(TermDesc)
      query-: Term;
   END;

   FieldTail= POINTER TO RECORD(TermDesc)
   END;

   Field*= POINTER TO RECORD(SubTermDesc) (* ADT Field *)
      tail: FieldTail;
   END;

   Name*= POINTER TO NameDesc;            (* ADT Name *)
   NameDesc*= RECORD(TermDesc)
      age-: INTEGER;
   END;

   Equation= POINTER TO RECORD(TermDesc)
      param: Name;
      next: Equation;
   END;
   
   Tree*= POINTER TO TreeDesc;            (* ADT Tree *)
   TreeDesc*= RECORD(TermDesc)
      attributes: Equation;
      constant: BOOLEAN;
   END;

   Atomic*= POINTER TO AtomicDesc;        (* ADT Atomic *)
   AtomicDesc*= RECORD(TermDesc)
   END;

   OpenTree*= POINTER TO RECORD(TreeDesc) (* ADT OpenTree *)
   END;

   Class*= POINTER TO ClassDesc;          (* ADT Class *)
   ClassDesc*= RECORD(TreeDesc)
   END;

   ClosedClass*= POINTER TO ClosedClassDesc;   (* ADT ClosedClass *)
   ClosedClassDesc*= RECORD(ClassDesc)
   END;

   Block*= POINTER TO RECORD(TreeDesc)
   END;

   HandlerType*= PROCEDURE;

   SystemTerm*= POINTER TO RECORD(TermDesc)   (* ADT SystemTerm *)
      handler: HandlerType;
   END;

   Disjunction*= POINTER TO RECORD(TermDesc)       (* ADT Disjunction *)
      alternative-: Term;
   END;

   TermBackup= NameDesc;
   
   TermStack*= POINTER TO TermStackDesc;
   TermStackDesc= RECORD
      top-: Term;
      rest-: TermStack;
   END;
VAR
   stack: POINTER TO ARRAY MaxStack OF TermBackup;
   continuation-,paramStack*: TermStack;
   sp, eldestAsked*: INTEGER;
   allConstant: BOOLEAN;

   otherwise*: Name;
   lastResult-, lastAtom-, Failure*, result*: Term;
   failName*: Name;
   Undefined-, Variable-: SystemTerm;
   LocalRestore, StackRestore, FunctionResult: SystemTerm;
   GuardTrap*, MatchTrap: SystemTerm;

PROCEDURE Push*(t: Term);
VAR
   newStack: TermStack;
BEGIN
   IF t#NIL THEN
      NEW(newStack);
      newStack.top:= t;
      newStack.rest:= continuation;
      continuation:= newStack;
   END;
END Push;


PROCEDURE (t: Term) Init*(ind: Term);
BEGIN
   t.indirection:= ind;
END Init;

PROCEDURE (t: Term) Reduce*;
BEGIN
   t.indirection.Reduce;
END Reduce;

PROCEDURE (t: Term) Value*(): Term;
VAR
   spOld,spNew: INTEGER;
   contOld: TermStack;
BEGIN
   spOld:= sp;
   contOld:= continuation;
   Push(FunctionResult);
   t.Reduce;
   spNew:= sp;
   ASSERT((sp=spOld) & (continuation=contOld));
   RETURN result
END Value;

PROCEDURE (t: Term) Evaluate*(query: Term): Term;
VAR
   spOld,spNew: INTEGER;
   contOld,contNew: TermStack;
BEGIN
   spOld:= sp;
   contOld:= continuation;
   Push(FunctionResult);
   Push(query);
   t.Reduce;
   spNew:= sp;
   contNew:= continuation;
   ASSERT((sp=spOld) & (continuation=contOld));
   RETURN result
END Evaluate;

PROCEDURE (t: Term) Actual*(): Term;
BEGIN
   RETURN t
END Actual;

PROCEDURE Continue*;
VAR
   spOld,spNew: INTEGER;
   next: Term;
   newTop: TermStack;
BEGIN
   spOld:= sp;
   next:= continuation.top;
   continuation:= continuation.rest;
   IF lastResult IS Atomic THEN
      NEW(newTop);
      newTop.top:= lastResult;
      newTop.rest:= paramStack;
      paramStack:= newTop;
      next.Reduce;
      paramStack:= paramStack.rest;
   ELSE
      next.Reduce;
   END;
   spNew:= sp;
   ASSERT(spNew=spOld, 255);
END Continue;

PROCEDURE Continued*(): BOOLEAN;
BEGIN
   IF continuation.top=FunctionResult THEN
      continuation:= continuation.rest;
      RETURN FALSE
   ELSE
      Continue;
      RETURN TRUE
   END;
END Continued;

PROCEDURE ResultHandler*;
BEGIN
   result:= lastResult;
END ResultHandler;

PROCEDURE Fail*;
VAR
   spOld: INTEGER;
BEGIN
   WHILE continuation.top#FunctionResult DO
      continuation:= continuation.rest;
   END;
   continuation:= continuation.rest;
   result:= Failure;
END Fail;


PROCEDURE (t: Name) Init*(contents: Term);
BEGIN
   t.Init^(contents);
   t.age:= 0;
END Init;

PROCEDURE (t: Name) Actual*(): Term;
BEGIN
   IF t.indirection IS SystemTerm THEN
      RETURN t
   ELSIF t.indirection IS Name THEN
      ASSERT(t.indirection#t);
      RETURN t.indirection.Actual()
   ELSE
      RETURN t.indirection
   END;
END Actual;

PROCEDURE (t: Name) Assign*(contents: Term);
BEGIN
(*   ASSERT(contents#t); *)
   INC(sp);
   stack[sp].indirection:= t.indirection;
   stack[sp].age:= t.age;
   t.indirection:= contents;
   t.age:= sp;
END Assign;

PROCEDURE (t: Name) Restore*();
BEGIN
   ASSERT(sp>0);
   ASSERT(t.age=sp);
   t.indirection:= stack[sp].indirection;
   t.age:= stack[sp].age;
   DEC(sp);
END Restore;

PROCEDURE (t: Name) Reduce*;
VAR
   saveLastName: Term;
   spOld,spNew: INTEGER;
BEGIN
   spOld:= sp;
   saveLastName:= lastResult;
   lastResult:= t;
   t.indirection.Reduce;
   lastResult:= saveLastName;
   IF t.age<eldestAsked THEN
      eldestAsked:= t.age;
   END;
   spNew:= sp;
   ASSERT(spOld=spNew);
END Reduce;


PROCEDURE (t: SubTerm) Reduce*;
BEGIN
   IF t.query=NIL THEN
      t.Reduce^;
   ELSE
      Push(t.query);
      t.indirection.Reduce;
   END;
END Reduce;

PROCEDURE (t: SubTerm) Actual*(): Term;
VAR
   newTerm: SubTerm;
BEGIN
   IF t.query=NIL THEN
      RETURN t
   END;
   result:= t.query.Actual();
   IF result=t.query THEN
      RETURN t
   ELSE
      NEW(newTerm);
      newTerm.indirection:= t.indirection;
      newTerm.query:= result;
      RETURN newTerm
   END;
END Actual;

PROCEDURE (t: SubTerm) InitQuery*(query: Term);
BEGIN
   t.query:= query;
END InitQuery;


PROCEDURE (t: Field) Actual*(): Term;
VAR
   spOld: INTEGER;
BEGIN
   spOld:= sp;
   RETURN t.indirection.Evaluate(t.tail)
END Actual;

PROCEDURE (t: Field) InitQuery*(query: Term);
VAR
   newTerm: FieldTail;
BEGIN
   NEW(newTerm);
   newTerm.indirection:= query;
   t.query:= query;
   t.tail:= newTerm;
END InitQuery;


PROCEDURE (t: FieldTail) Reduce*;
BEGIN
   IF ~Continued() THEN
      result:= t.indirection.Actual();
   ELSE
      HALT(255);
   END;
END Reduce;


PROCEDURE (t: Equation) Association(param: Name): Term;
BEGIN
   WHILE (t#NIL) & (t.param#param) DO
      t:= t.next;
   END;
   IF t=NIL THEN
      RETURN NIL
   ELSE
      RETURN t.indirection.Actual()
   END;
END Association;

PROCEDURE (t: Equation) Unfold();
VAR
   follow: Equation;
BEGIN
   follow:= t;
   REPEAT
      follow.param.Assign(follow.indirection);
      follow:= follow.next;
   UNTIL follow=NIL;
END Unfold;

PROCEDURE (t: Equation) UnfoldActual();
VAR
   spStart: INTEGER;
   swap: Term;
   follow: Equation;
BEGIN
   spStart:= sp;
   follow:= t;
   REPEAT
      INC(sp);
      stack[sp].indirection:= follow.indirection.Actual();
      follow:= follow.next;
   UNTIL follow=NIL;
   REPEAT
      INC(spStart);
      swap:= t.param.indirection;
      t.param.indirection:= stack[spStart].indirection;
      stack[spStart].indirection:= swap;
      stack[spStart].age:= t.param.age;
      t.param.age:= spStart;
      t:= t.next;
   UNTIL t=NIL;
END UnfoldActual;

PROCEDURE (t: Equation) Restore();
BEGIN
   sp:= t.param.age-1;
   REPEAT
      t.param.indirection:= stack[t.param.age].indirection;
      t.param.age:= stack[t.param.age].age;
      t:= t.next;
   UNTIL t=NIL;
END Restore;

PROCEDURE (t: Equation) Enrich(VAR base: Term);
VAR
   oldEdges, newEdges: Equation;
   spStart: INTEGER;
   newTerm: OpenTree;
BEGIN
   WITH base: OpenTree DO
      oldEdges:= base.attributes;
      newEdges:= oldEdges;
      spStart:= t.param.age;
      WHILE oldEdges#NIL DO
         IF oldEdges.param.age>=spStart THEN
            oldEdges.param.age:= -oldEdges.param.age;
         END;
         oldEdges:= oldEdges.next;
      END;
      WHILE t#NIL DO
         IF t.param.age<0 THEN
            t.param.age:= -t.param.age;
         ELSE
            oldEdges:= newEdges;
            NEW(newEdges);
            newEdges.param:= t.param;
            newEdges.indirection:= t.param.indirection;
            newEdges.next:= oldEdges;
         END;
         t:= t.next;
      END;
      base.attributes:= newEdges;
      base.constant:= FALSE;
   ELSE
      IF base IS Name THEN
         NEW(newTerm);
         newTerm.indirection:= base;
         newTerm.constant:= FALSE;
         newTerm.attributes:= NIL;
         oldEdges:= t;
         WHILE oldEdges#NIL DO
            NEW(newEdges);
            newEdges.param:= oldEdges.param;
            newEdges.indirection:= oldEdges.param.indirection;
            newEdges.next:= newTerm.attributes;
            newTerm.attributes:= newEdges;
            oldEdges:= oldEdges.next;
         END;
         base:= newTerm;
      END;
   END;
END Enrich;

PROCEDURE (t: Equation) ActualizeUsing(base: Equation);
VAR
   follow: Equation;
   link: Name;
   spStart: INTEGER;
BEGIN
   spStart:= sp;
   follow:= t;
   WHILE follow#NIL DO
      IF follow.indirection IS Name THEN
         link:= follow.indirection(Name);
         link.age:= -link.age-1;
      END;
      follow:= follow.next;
   END;
   WHILE base#NIL DO
      IF base.param.age<0 THEN
         base.param.Assign(base.indirection);
      END;
      base:= base.next;
   END;
   follow:= t;
   WHILE follow#NIL DO
      IF follow.indirection IS Name THEN
         link:= follow.indirection(Name);
         IF link.age<0 THEN
            link.age:= -link.age-1;
         ELSE
            follow.param.indirection:= link.indirection;
            follow.indirection:= link.indirection;
            link.indirection:= stack[link.age].indirection;
            link.age:= -stack[link.age].age-1;
         END;
      END;
      follow:= follow.next;
   END;
   sp:= spStart;
END ActualizeUsing;

PROCEDURE (t: Equation) Actual(): Term;
VAR
   newEdge: Equation;
   newMeaning,actualRest: Term;
BEGIN
   newMeaning:= t.indirection.Actual();
   IF newMeaning=t.indirection THEN
      IF t.next#NIL THEN
         actualRest:= t.next.Actual();
         IF actualRest#t.next THEN
            NEW(newEdge);
            newEdge.param:= t.param;
            newEdge.indirection:= newMeaning;
            newEdge.next:= actualRest(Equation);
            RETURN newEdge
         END;
      END;
      IF t.indirection IS Name THEN
         allConstant:= FALSE;
      END;
      RETURN t
   ELSE
      NEW(newEdge);
      newEdge.param:= t.param;
      newEdge.indirection:= newMeaning;
      IF t.next=NIL THEN
         newEdge.next:= NIL;
      ELSE
         actualRest:= t.next.Actual();
         newEdge.next:= actualRest(Equation);
      END;
      RETURN newEdge
   END;
END Actual;


PROCEDURE (t: Tree) AddProperty*(param: Name; meaning: Term);
VAR
   newEdge: Equation;
BEGIN
   newEdge:= t.attributes;
   WHILE (newEdge#NIL) & (newEdge.param#param) DO
      newEdge:= newEdge.next;
   END;
   IF newEdge=NIL THEN
      NEW(newEdge);
      newEdge.param:= param;
      newEdge.next:= t.attributes;
      t.attributes:= newEdge;
   END;
   newEdge.indirection:= meaning;
END AddProperty;

PROCEDURE (t: Tree) RemoveProperty*(param: Name);
VAR
   follow,oldEdge: Equation;
BEGIN
   oldEdge:= t.attributes;
   WHILE (oldEdge#NIL) & (oldEdge.param#param) DO
      follow:= oldEdge;
      oldEdge:= oldEdge.next;
   END;
   IF oldEdge#NIL THEN
      IF oldEdge=t.attributes THEN
         t.attributes:= oldEdge.next;
      ELSE
         follow.next:= oldEdge.next;
      END;
   END;
END RemoveProperty;

PROCEDURE Attributed(VAR root: Term; prop: Name; value: Term);
VAR
   newTerm: OpenTree;
BEGIN
   NEW(newTerm);
   IF root IS Name THEN
      newTerm.indirection:= root;
      newTerm.constant:= FALSE;
      newTerm.attributes:= NIL;
   ELSIF root IS OpenTree THEN
      newTerm^:= root(OpenTree)^;
   ELSE
      RETURN
   END;
   newTerm.AddProperty(prop,value);
   root:= newTerm;
END Attributed;

PROCEDURE (t: Tree) Reduce*;
VAR
   spOld,spNew: INTEGER;
   attr,follow,newEq: Equation;
   newTerm: OpenTree;
BEGIN
   spOld:= sp;
   attr:= t.attributes;
   IF attr=NIL THEN
      t.Reduce^;
   ELSE
      attr.UnfoldActual();
      t.indirection.Reduce;
      attr.Enrich(result);
      attr.Restore();
   END;
   spNew:= sp;
   ASSERT(spOld=spNew);
END Reduce;

PROCEDURE (t: Tree) Actual*(): Term;
VAR
   newTerm: Tree;
   newAttributes: Term;
BEGIN
   IF t.constant OR (t.attributes=NIL) THEN
      t.constant:= TRUE;
      RETURN t
   END;
   allConstant:= TRUE;
   newAttributes:= t.attributes.Actual();
   IF allConstant & (newAttributes=t.attributes) THEN
      t.constant:= TRUE;
      RETURN t
   ELSE
      NEW(newTerm);
      newTerm.indirection:= t.indirection;
      newTerm.attributes:= newAttributes(Equation);
(*      newTerm.constant:= TRUE; *)
      RETURN newTerm
   END;
END Actual;

PROCEDURE (t: Tree) Init*(ind: Term);
BEGIN
   t.indirection:= ind;
   t.attributes:= NIL;
   t.constant:= FALSE;
END Init;

PROCEDURE (t: Tree) ProcessAttributes*(proc: PROCEDURE(attr: Name; VAR meaning: Term));
VAR
   follow: Equation;
BEGIN
   follow:= t.attributes;
   WHILE follow#NIL DO
      proc(follow.param,follow.indirection);
      follow:= follow.next;
   END;
END ProcessAttributes;


PROCEDURE (t: Class) Reduce*;
VAR
   spOld: INTEGER;
   attr: Equation;
BEGIN
   spOld:= sp;
   attr:= t.attributes;
   IF attr=NIL THEN
      t.Reduce^;
   ELSE
      attr.Unfold();
      Continue;
      attr.Restore();
   END;
   ASSERT(spOld=sp);
END Reduce;

PROCEDURE (t: Class) Actual*(): Term;
BEGIN
   RETURN t
END Actual;


PROCEDURE (t: ClosedClass) Reduce*;
VAR
   query,root: Term;
BEGIN
   query:= continuation.top;
   root:= query;
   WHILE ~(root IS Name) DO
      root:= root.indirection;
   END;
   WITH root: Name DO
      result:= t.attributes.Association(root);
      IF result=NIL THEN
         result:= t.attributes.Association(otherwise);
         IF result=NIL THEN
            Continue;
            RETURN
         END;
      END;
      root.Assign(Undefined);
      continuation:= continuation.rest;
      Push(result);
      query.Reduce();
      root.Restore();
   END;
END Reduce;


PROCEDURE (t: SystemTerm) Reduce*;
BEGIN
   t.handler;
END Reduce;

PROCEDURE (t: SystemTerm) InitHandler*(h: HandlerType);
BEGIN
   t.handler:= h;
END InitHandler;


PROCEDURE (t: Atomic) Reduce*;
VAR
   saveLastAtom: Term;
BEGIN
   saveLastAtom:= lastAtom;
   lastAtom:= t;
   t.indirection.Reduce;
   lastAtom:= saveLastAtom;
END Reduce;


PROCEDURE (t: Atomic) Compare*(reference: Term; VAR lessEq,grEq: BOOLEAN);
BEGIN
   lessEq:= (t.indirection=reference.indirection);
   grEq:= lessEq;
END Compare;


PROCEDURE AtomicHandler*;
VAR
   saveLastResult: Term;
BEGIN
   eldestAsked:= Fixed;
   saveLastResult:= lastResult;
   lastResult:= lastAtom;
   Continue;
   lastResult:= saveLastResult;
END AtomicHandler;


PROCEDURE Equal*(t1,t2: Term): BOOLEAN;
VAR
   lessEq,greaterEq: BOOLEAN;

   PROCEDURE AttrEqual(attr1,attr2: Equation): BOOLEAN;
   VAR
      oldSp: INTEGER;
      copy: Equation;
   BEGIN
      copy:= attr1;
      oldSp:= sp;
      copy.Unfold();
      WHILE (attr1#attr2) & (attr2#NIL) & (attr2.param.age>oldSp) &
            Equal(attr2.indirection,attr2.param.indirection) DO
         attr1:= attr1.next;
         attr2:= attr2.next;
      END;
      copy.Restore();
      RETURN attr1=attr2
   END AttrEqual;

BEGIN
   IF t1=t2 THEN
      RETURN TRUE
   END;
   IF t1.indirection#t2.indirection THEN
      RETURN FALSE
   END;
   WITH t1: Tree DO
      WITH t2: Tree DO
         IF t1.attributes#NIL THEN
            RETURN AttrEqual(t1.attributes,t2.attributes)
         END;
      ELSE
         RETURN FALSE
      END;
   ELSE
      WITH t1: Atomic DO
         t1.Compare(t2,lessEq,greaterEq);
         RETURN lessEq&greaterEq
      ELSE
         RETURN TRUE
      END;
   END;
END Equal;


PROCEDURE EnvironmentPath*(t: Name): SubTerm;
VAR
   result,previous: SubTerm;
   position: INTEGER;
BEGIN
   NEW(result);
   result.Init(t.indirection);
   position:= t.age;
   WHILE position#0 DO
      previous:= result;
      NEW(result);
      result.indirection:= stack[position].indirection;
      result.query:= previous;
      position:= stack[position].age;
   END;
   RETURN result
END EnvironmentPath;


PROCEDURE RestoreReversed(list: Equation);
BEGIN
   IF list#NIL THEN
      RestoreReversed(list.next);
      list.param.Assign(continuation.top);
      continuation:= continuation.rest;
   END;
END RestoreReversed;

PROCEDURE RestoreLocals;
VAR
   locals: Equation;
BEGIN
   locals:= continuation.top(Equation);
   continuation:= continuation.rest;
   RestoreReversed(locals);
   Continue;
   WHILE locals#NIL DO
      locals.param.Restore();
      locals:= locals.next;
   END;
END RestoreLocals;

PROCEDURE RestoreLocal;
VAR
   local: Name;
BEGIN
   local:= continuation.top(Name);
   continuation:= continuation.rest;
   local.Assign(continuation.top);
   continuation:= continuation.rest;
   Continue;
   local.Restore();
END RestoreLocal;

PROCEDURE PushLocal*(t: Name);
BEGIN
   Push(t.indirection);
   Push(t);
   Push(LocalRestore);
END PushLocal;


PROCEDURE (t: Block) Reduce*;
VAR
   follow: Equation;
   newTerm: Name;
BEGIN
   follow:= t.attributes;
   IF follow#NIL THEN
      REPEAT
         Push(follow.param.indirection);
         IF follow.indirection=Variable THEN
            NEW(newTerm);
            newTerm.Init(Variable);
            follow.param.Assign(newTerm);
         ELSE
            follow.param.Assign(follow.indirection.Actual());
         END;
         follow:= follow.next;
      UNTIL follow=NIL;
      Push(t.attributes);
      Push(StackRestore);
      t.indirection.Reduce;
      IF result IS Tree THEN
         t.attributes.ActualizeUsing(result(Tree).attributes);
      END;
      t.attributes.Enrich(result);
      t.attributes.Restore;
   ELSE
      t.indirection.Reduce;
   END;
END Reduce;


PROCEDURE GuardHandler*;
VAR
   follow: Equation;
   pattern: Term;
   newTerm: OpenTree;
BEGIN
   pattern:= continuation.top;
   continuation:= continuation.rest;
   IF lastResult=pattern.indirection THEN
      IF pattern IS Tree THEN
         follow:= pattern(Tree).attributes;
         WHILE follow#NIL DO
            Push(follow.indirection);
            Push(follow.param.indirection);
            Push(MatchTrap);
            follow:= follow.next;
         END;
      END;
      Continue;
   ELSIF (lastResult IS Name) & 
         (lastResult.indirection=Variable) THEN
      WITH lastResult: Name DO
         lastResult.Assign(pattern.Actual());
         Continue;
         Attributed(result,lastResult,lastResult.indirection);
         lastResult.Restore();
      END;
   ELSIF (pattern IS Atomic) & Equal(pattern,lastResult) THEN
      Continue;
   ELSE
      Fail;
   END;
END GuardHandler;


PROCEDURE MatchHandler;
VAR
   lhs,pattern: Term;
   r: TermStack;
BEGIN
   lhs:= continuation.top;
   r:= continuation;
   continuation:= continuation.rest;
   pattern:= continuation.top;
   IF pattern IS Name THEN
      continuation:= continuation.rest;
      pattern:= pattern.Value();
      IF (pattern IS Name) & (pattern.indirection=Variable) THEN
         WITH pattern: Name DO
            pattern.Assign(lhs);
            Continue;
            pattern.Restore();
            Attributed(result,pattern,lhs);
         END;
         RETURN
      ELSE
         Push(pattern);
      END;
   END;
   Push(GuardTrap);
   lhs.Reduce;
END MatchHandler;


PROCEDURE (t: Disjunction) Reduce*;
VAR
   oldCont: TermStack;
BEGIN
   oldCont:= continuation;
   t.indirection.Reduce;
   IF result=Failure THEN
      continuation:= oldCont;
      t.alternative.Reduce;
   END;
END Reduce;

PROCEDURE (t: Disjunction) InitAlternative*(alt: Term);
BEGIN
   t.alternative:= alt;
END InitAlternative;

PROCEDURE Unify*(t1,t2: Term);
BEGIN
   Push(t2);
   Push(t1);
   MatchHandler;
END Unify;

PROCEDURE MakeLocalBlock*(locals,body: Term): Term;
VAR
   newTerm: Block;
BEGIN
   IF locals=NIL THEN
      RETURN body
   END;
   NEW(newTerm);
   newTerm.Init(body);
   IF locals IS Tree THEN
      locals:= locals(Tree).attributes;
   END;
   newTerm.attributes:= locals(Equation);
   RETURN newTerm
END MakeLocalBlock;


PROCEDURE MakeAlternative*(pattern,ifMatch: Term): Term;
VAR
   sub1,sub2: SubTerm;
(*   newDis: Disjunction; *)
   acc: Equation;

   PROCEDURE  Locals(t: Equation);
   VAR
      newEq: Equation;
   BEGIN
      IF t#NIL THEN
         IF t.indirection IS Name THEN
            IF (acc=NIL) OR (acc.Association(t.indirection(Name))=NIL) THEN
               NEW(newEq);
               newEq.param:= t.indirection(Name);
               newEq.indirection:= Variable;
               newEq.next:= acc;
               acc:= newEq;
            END;
         ELSIF t.indirection IS Tree THEN
            Locals(t.indirection(Tree).attributes);
         END;
         Locals(t.next);
      END;
   END Locals;
BEGIN
   WITH pattern: Tree DO
      NEW(sub1);
      NEW(sub2);
      sub1.query:= ifMatch;
      sub2.query:= pattern;
      sub2.indirection:= GuardTrap;
      sub1.indirection:= sub2;
      acc:= NIL;
      Locals(pattern.attributes);
(*      IF noMatch=NIL THEN *)
         RETURN MakeLocalBlock(acc,sub1)
(*      END;
      NEW(newDis);
      newDis.indirection:= MakeLocalBlock(acc,sub1);
      newDis.alternative:= noMatch;
      RETURN newDis *)
   ELSE
      RETURN ifMatch
   END;
END MakeAlternative;

BEGIN
   NEW(stack);
   sp:= 0;
   continuation:= NIL;
   NEW(FunctionResult);
   FunctionResult.Init(NIL);
   FunctionResult.InitHandler(ResultHandler);
   lastAtom:= NIL;
   NEW(lastResult);
   lastResult.Init(NIL);
   NEW(Variable);
   Variable.Init(NIL);
   Variable.InitHandler(Continue);
   NEW(Undefined);
   Undefined.Init(NIL);
   Undefined.InitHandler(Continue);
   NEW(LocalRestore);
   LocalRestore.Init(NIL);
   LocalRestore.InitHandler(RestoreLocal);
   NEW(StackRestore);
   StackRestore.Init(NIL);
   StackRestore.InitHandler(RestoreLocals);
   NEW(GuardTrap);
   GuardTrap.Init(NIL);
   GuardTrap.InitHandler(GuardHandler);
   NEW(MatchTrap);
   MatchTrap.Init(NIL);
   MatchTrap.InitHandler(MatchHandler);
END AGRS.

