MODULE Library;
IMPORT AGRS,Names,Texts,TextFrames;


CONST 
   (* Kodovi gresaka koji su sadrzani u tipu podataka Error. *)
   NotLogicalType*= 0;
   NotNumberType*= 1;
   NotCharacterType*= 2;
   NotStringType*= 3;
   NotTextType*= 4;
   NotFound*= 5;
   SyntaxError*= 6;

   CharSetLength= 256 DIV (MAX(SET)+1);

TYPE
   Term= AGRS.Term;
   ErrorType= INTEGER;

   NamesType= POINTER TO RECORD(AGRS.ClosedClassDesc)
   END;

   Number*= POINTER TO RECORD(AGRS.AtomicDesc)
      value*: INTEGER;
   END;

   String*= POINTER TO RECORD(AGRS.AtomicDesc)
      value-: Names.CharPtr;
   END;

   Text*= POINTER TO RECORD(AGRS.AtomicDesc)
      base-: Texts.Text;
      startOffset-,endOffset-: LONGINT;
   END;

   Character*= POINTER TO RECORD(AGRS.AtomicDesc)
      value-: CHAR;
   END;

   CharSet*= POINTER TO RECORD( AGRS.AtomicDesc)
      value-: ARRAY CharSetLength OF SET;
   END;

   Error*= POINTER TO RECORD(AGRS.AtomicDesc)
      value-: ErrorType;
   END;
   
   BinOp= POINTER TO RECORD(AGRS.TermDesc)
   END;
VAR
   TrueDef: Term;

   disTerm: AGRS.Disjunction;
   NamesTerm: NamesType;

   atomicName,numberName*,errorName*: AGRS.Name;
   charName*,stringName*,textName*,charSetName*: AGRS.Name;
   ifName,orName,andName,notName,testName,yesName,noName: AGRS.Name;
   addName*,subName*,mulName*,divName,modName: AGRS.Name;
   argName1*,argName2*: AGRS.Name;
   equalName,lessName,greaterName,lessEqName,grEqName: AGRS.Name;
   trueName*,disName,unifyName: AGRS.Name;
   abortName*,findName,nameName: AGRS.Name;
   carName,cdrName,consName,nilName: AGRS.Name;
   namesName: AGRS.Name;
   


PROCEDURE NewNumber*(v: INTEGER): Number;
VAR
   result: Number;
BEGIN
   NEW(result);
   result.Init(numberName);
   result.value:= v;
   AGRS.eldestAsked:= AGRS.Fixed;
   RETURN result;
END NewNumber;

PROCEDURE NewString*(v: Names.CharPtr): String;
VAR
   result: String;
BEGIN
   NEW(result);
   result.Init(stringName);
   result.value:= v;
   AGRS.eldestAsked:= AGRS.Fixed;
   RETURN result;
END NewString;

PROCEDURE NewChar*(v: CHAR): Character;
VAR
   result: Character;
BEGIN
   NEW(result);
   result.Init(charName);
   result.value:= v;
   AGRS.eldestAsked:= AGRS.Fixed;
   RETURN result;
END NewChar;

PROCEDURE NewCharSet*(): CharSet;
VAR
   result: CharSet;
   i: INTEGER;
BEGIN
   NEW(result);
   result.Init(charSetName);
   FOR i:= 0 TO CharSetLength-1 DO
      result.value[i]:= {};
   END;
   AGRS.eldestAsked:= AGRS.Fixed;
   RETURN result;
END NewCharSet;

   
PROCEDURE (t: String) Length*(): LONGINT;
VAR
   i: LONGINT;
   str: Names.CharPtr;
BEGIN
   i:= 0;
   str:= t.value;
   WHILE str[i]#0X DO
      INC(i);
   END;
   RETURN i
END Length;


PROCEDURE (t: CharSet) Include*(ch: CHAR);
BEGIN
   INCL(t.value[ORD(ch) DIV (MAX(SET)+1)],ORD(ch) MOD (MAX(SET)+1));
END Include;

PROCEDURE (t: CharSet) Complement*();
VAR
   i: INTEGER;
BEGIN
   FOR i:= 0 TO CharSetLength-1 DO
      t.value[i]:= -t.value[i];
   END;
END Complement;

PROCEDURE NewError*(v: ErrorType): Error;
VAR
   result: Error;
BEGIN
   NEW(result);
   result.Init(errorName);
   AGRS.eldestAsked:= AGRS.Fixed;
   result.value:= v;
   RETURN result
END NewError;

PROCEDURE SubText*(txt: Texts.Text; startPos,endPos: LONGINT): Text;
VAR
   newTerm: Text;
BEGIN
   NEW(newTerm);
   newTerm.Init(textName);
   newTerm.base:= txt;
   newTerm.startOffset:= startPos;
   newTerm.endOffset:= endPos;
   RETURN newTerm
END SubText;


PROCEDURE (t: Text) AppendText*(appendage: Text);
VAR
   temp: Texts.Buffer;
   newText: Texts.Text;
BEGIN
   IF (t.base=appendage.base) & (t.endOffset=appendage.startOffset) THEN
      t.endOffset:= appendage.endOffset;
   ELSE
      newText:= TextFrames.Text("");
      NEW(temp);
      Texts.OpenBuf(temp);
      Texts.Save(t.base,t.startOffset,t.endOffset,temp);
      Texts.Save(appendage.base,appendage.startOffset,appendage.endOffset,temp);
      Texts.Append(newText,temp);
      t.base:= newText;
      t.startOffset:= 0;
      t.endOffset:= newText.len;
   END;
END AppendText;

PROCEDURE (t: Text) AppendBuffer*(appendage: Texts.Buffer);
VAR
   newText: Texts.Text;
BEGIN
   IF t.endOffset=t.base.len THEN
      Texts.Append(t.base,appendage);
      t.endOffset:= t.base.len;
   ELSE
      newText:= TextFrames.Text("");
      Texts.Append(newText,appendage);
      t.base:= newText;
      t.startOffset:= 0;
      t.endOffset:= newText.len;
   END;
END AppendBuffer;


PROCEDURE (t: NamesType) Evaluate*(query: Term): Term;
BEGIN
   RETURN NewString(Names.NameSpelling(query.indirection))
END Evaluate;


PROCEDURE pType;
VAR
   newTerm: AGRS.OpenTree;
BEGIN
   NEW(newTerm);
   newTerm.Init(AGRS.lastResult);
   AGRS.result:= newTerm;
END pType;


PROCEDURE (t: Character) Compare*(reference: Term; VAR lessEq,grEq: BOOLEAN);
BEGIN
   WITH reference: Character DO
      lessEq:= t.value<=reference.value;
      grEq:= t.value>=reference.value;
   ELSE
      WITH reference: String DO
         lessEq:= t.value<=reference.value[0];
         grEq:= t.value>=reference.value[0];
         IF lessEq & grEq THEN
            grEq:= reference.value[1]=0X;
         END;
      ELSE
         lessEq:= FALSE;
         grEq:= FALSE;
      END;
   END;
END Compare;

PROCEDURE (t: String) Compare*(reference: AGRS.Term; VAR lessEq,grEq: BOOLEAN);
VAR
   i: INTEGER;
BEGIN
   WITH reference: Character DO
      lessEq:= t.value[0]<=reference.value;
      grEq:= t.value[0]>=reference.value;
      IF lessEq & grEq THEN
         lessEq:= t.value[1]=0X;
      END;
   ELSE
      WITH reference: String DO
         i:= 0;
         WHILE (t.value[i]=reference.value[i]) & (t.value[i]#0X) DO
            INC(i);
         END;
         lessEq:= (t.value[i]<=reference.value[i]);
         grEq:= (t.value[i]>=reference.value[i]);
      ELSE
         lessEq:= FALSE;
         grEq:= FALSE;
      END;
   END;
END Compare;

PROCEDURE (t: Number) Compare*(reference: Term; VAR lessEq,grEq: BOOLEAN);
BEGIN
   WITH reference: Number DO
      lessEq:= t.value<=reference.value;
      grEq:= t.value>=reference.value;
   ELSE
      lessEq:= FALSE;
      grEq:= FALSE;
   END;
END Compare;

PROCEDURE (t: CharSet) Compare*(reference: Term; VAR lessEq,grEq: BOOLEAN);
VAR
   i: INTEGER;
BEGIN
   lessEq:= TRUE;
   grEq:= TRUE;
   WITH reference: CharSet DO
      FOR i:= 0 TO CharSetLength-1 DO
         IF t.value[i]-reference.value[i]#{} THEN
            lessEq:= FALSE;
         END;
         IF reference.value[i]-t.value[i]#{} THEN
            grEq:= FALSE;
         END;
      END;
   ELSE
   END;
END Compare;

PROCEDURE (t: Error) Compare*(reference: Term; VAR lessEq,grEq: BOOLEAN);
BEGIN
   WITH reference: Error DO
      lessEq:= t.value<=reference.value;
      grEq:= t.value>=reference.value;
   ELSE
      lessEq:= FALSE;
      grEq:= FALSE;
   END;
END Compare;


PROCEDURE pEqual;
VAR
   t1,t2: AGRS.Term;
BEGIN
   t1:= argName1.Value();
   t2:= argName2.Value();
   IF AGRS.Equal(t1,t2) THEN
      TrueDef.Reduce;
   ELSE
      AGRS.Fail;
   END;
END pEqual;

PROCEDURE pLess;
VAR
   t1,t2: AGRS.Term;
   lessEq,grEq: BOOLEAN;
BEGIN
   t1:= argName1.Value();
   WITH t1: AGRS.Atomic DO
      t2:= argName2.Value();
      t1.Compare(t2,lessEq,grEq);
      IF lessEq & ~grEq THEN
         TrueDef.Reduce;
         RETURN
      END;
   END;
   AGRS.Fail;
END pLess;

PROCEDURE pGreater;
VAR
   t1,t2: AGRS.Term;
   lessEq,grEq: BOOLEAN;
   oldStack: AGRS.TermStack;
BEGIN
   t1:= argName1.Value();
   WITH t1: AGRS.Atomic DO
      t2:= argName2.Value();
      t1.Compare(t2,lessEq,grEq);
      IF ~lessEq & grEq THEN
         TrueDef.Reduce;
         RETURN
      END;
   END;
   AGRS.Fail;
END pGreater;

PROCEDURE pLessEq;
VAR
   t1,t2: AGRS.Term;
   lessEq,grEq: BOOLEAN;
BEGIN
   t1:= argName1.Value();
   WITH t1: AGRS.Atomic DO
      t2:= argName2.Value();
      t1.Compare(t2,lessEq,grEq);
      IF lessEq THEN
         TrueDef.Reduce;
         RETURN
      END;
   END;
   AGRS.Fail;
END pLessEq;

PROCEDURE pGrEq;
VAR
   t1,t2: AGRS.Term;
   lessEq,grEq: BOOLEAN;
BEGIN
   t1:= argName1.Value();
   WITH t1: AGRS.Atomic DO
      t2:= argName2.Value();
      t1.Compare(t2,lessEq,grEq);
      IF grEq THEN
         TrueDef.Reduce;
         RETURN
      END;
   END;
   AGRS.Fail;
END pGrEq;

PROCEDURE pNot;
BEGIN
   AGRS.result:= argName1.Value();
   IF AGRS.result.indirection=trueName THEN
      AGRS.result:= AGRS.Failure;
   ELSIF AGRS.result.indirection=AGRS.failName THEN
      AGRS.result:= TrueDef;
   ELSE
      AGRS.result:= NewError(NotLogicalType);
   END;
   AGRS.result.Reduce;
END pNot;

PROCEDURE pAnd;
VAR
   eldest1: INTEGER;
BEGIN
   AGRS.result:= argName1.Value();
   IF AGRS.result.indirection=trueName THEN
      eldest1:= AGRS.eldestAsked;
      AGRS.result:= argName2.Value();
      IF eldest1<AGRS.eldestAsked THEN
         AGRS.eldestAsked:= eldest1;
      END;
   ELSIF AGRS.result.indirection#AGRS.failName THEN
      AGRS.result:= NewError(NotLogicalType);
   END;
   AGRS.result.Reduce;
END pAnd;

PROCEDURE pOr;
VAR
   eldest1: INTEGER;
BEGIN
   AGRS.result:= argName1.Value();
   IF AGRS.result.indirection=AGRS.failName THEN
      eldest1:= AGRS.eldestAsked;
      AGRS.result:= argName2.Value();
      IF eldest1<AGRS.eldestAsked THEN
         AGRS.eldestAsked:= eldest1;
      END;
   ELSIF AGRS.result.indirection#trueName THEN
      AGRS.result:= NewError(NotLogicalType);
   END;
   AGRS.result.Reduce;
END pOr;


PROCEDURE pIf;
VAR
   eldest1: INTEGER;
BEGIN
   AGRS.result:= testName.Value();
   eldest1:= AGRS.eldestAsked;
   IF AGRS.result.indirection=trueName THEN
      yesName.Reduce;
   ELSIF AGRS.result.indirection=AGRS.failName THEN
      noName.Reduce;
   ELSE
      AGRS.result:= NewError(NotLogicalType);
      AGRS.result.Reduce;
   END;
   IF eldest1<AGRS.eldestAsked THEN
      AGRS.eldestAsked:= eldest1;
   END;
END pIf;


PROCEDURE ExtractNumbers(VAR x,y:INTEGER):BOOLEAN;
VAR
   eldest1: INTEGER;
   arg: Term;
BEGIN
   arg:= argName1.Value();
   WITH arg: Number DO
      x:= arg.value;
   ELSE
      RETURN FALSE
   END;
   eldest1:= AGRS.eldestAsked;
   arg:= argName2.Value();
   WITH arg: Number DO
      y:= arg.value;
   ELSE
      RETURN FALSE
   END;
   IF eldest1<AGRS.eldestAsked THEN
      AGRS.eldestAsked:= eldest1;
   END;
   RETURN TRUE
END ExtractNumbers;

PROCEDURE ExtractNumbersFromStack(VAR x,y:INTEGER; VAR oldStack:AGRS.TermStack):BOOLEAN;
VAR
   arg: Term;
BEGIN
   IF (AGRS.paramStack=NIL) OR (AGRS.paramStack.rest=NIL) THEN
      RETURN FALSE
   END;
   oldStack:= AGRS.paramStack;
   arg:= AGRS.paramStack.top;
   WITH arg: Number DO
      x:= arg.value;
   ELSE
      RETURN FALSE
   END;
   AGRS.paramStack:= AGRS.paramStack.rest;
   arg:= AGRS.paramStack.top;
   WITH arg: Number DO
      y:= arg.value;
   ELSE
      RETURN FALSE
   END;
   AGRS.paramStack:= AGRS.paramStack.rest;
   RETURN TRUE
END ExtractNumbersFromStack;

PROCEDURE pAdd;
VAR
   x,y:INTEGER;
   newTerm: Term;
   oldStack: AGRS.TermStack;
BEGIN
   IF ExtractNumbers(x,y) THEN
      newTerm:= NewNumber(x+y);
      newTerm.Reduce;
   ELSE
      AGRS.Continue;
   END;
END pAdd;

PROCEDURE pSub;
VAR
   x,y:INTEGER;
   newTerm: Term;
BEGIN
   IF ExtractNumbers(x,y) THEN
      newTerm:= NewNumber(x-y);
      newTerm.Reduce;
   ELSE
      AGRS.Continue;
   END;
END pSub;

PROCEDURE pMul;
VAR
   x,y:INTEGER;
   newTerm: Term;
BEGIN
   IF ExtractNumbers(x,y) THEN
      newTerm:= NewNumber(x*y);
      newTerm.Reduce;
   ELSE
      AGRS.Continue;
   END;
END pMul;

PROCEDURE pDiv;
VAR
   x,y:INTEGER;
   newTerm: Term;
BEGIN
   IF ExtractNumbers(x,y) THEN
      newTerm:= NewNumber(x DIV y);
      newTerm.Reduce;
   ELSE
      AGRS.Continue;
   END;
END pDiv;

PROCEDURE pMod;
VAR
   x,y:INTEGER;
   newTerm: Term;
BEGIN
   IF ExtractNumbers(x,y) THEN
      newTerm:= NewNumber(x MOD y);
      newTerm.Reduce;
   ELSE
      AGRS.Continue;
   END;
END pMod;


PROCEDURE pFind;
VAR
   s,n: Term;
BEGIN
   s:= nameName.Value();
   WITH s: String DO
      n:= Names.FindPublicName(s.value^);
      IF n=NIL THEN
         n:= NewError(NotFound);
      END;
   ELSE
      n:= NewError(NotStringType);
   END;
   n.Reduce;
END pFind;

PROCEDURE pAbort;
VAR
   stack: AGRS.TermStack;
BEGIN
   stack:= AGRS.continuation;
   HALT(255)
END pAbort;

PROCEDURE pUnify;
BEGIN
   AGRS.Push(trueName);
   AGRS.Unify(argName1.indirection,argName2.Value());
END pUnify;

PROCEDURE (t: BinOp) Reduce*;
BEGIN
   AGRS.Push(t.indirection);
   AGRS.Push(argName2.indirection);
   argName1.Reduce;
END Reduce;

PROCEDURE AddBinOp(proc:AGRS.HandlerType; name,primName: ARRAY OF CHAR);
VAR
   newTerm: BinOp;
   newName: AGRS.Name;
BEGIN
   Names.AddSystemName(newName,primName,proc);
   NEW(newTerm);
   newTerm.Init(newName);
   Names.DefinePublicName(newName,name,newTerm);
END AddBinOp;

BEGIN
   Names.AddSystemName(atomicName,'AtomSystemRoot',AGRS.AtomicHandler);
   Names.DefinePublicName(textName,'TEXT',atomicName.indirection);
   Names.DefinePublicName(stringName,'STRING',atomicName.indirection);
   Names.DefinePublicName(charName,'CHAR',atomicName.indirection);
   Names.DefinePublicName(charSetName,'CharSET',atomicName.indirection);
   Names.DefinePublicName(errorName,'ERROR',atomicName.indirection);
   Names.DefinePublicName(numberName,'NUMBER',atomicName.indirection);

   Names.AddArgument(carName, 'Car');
   Names.AddArgument(cdrName, 'Cdr');
   Names.AddArgument(nilName, 'Nil');
   Names.AddArgument(consName, 'Cons');

   Names.AddArgument(trueName, 'True');
   NEW(TrueDef);
   TrueDef.Init(trueName);
   Names.AddSystemName(andName, 'And', pAnd);
   Names.AddSystemName(orName, 'Or', pOr);
   Names.AddSystemName(notName, 'Not', pNot);
   Names.AddSystemName(ifName, 'If', pIf);
   Names.AddArgument(testName, 'Test');
   Names.AddArgument(yesName, 'Yes');
   Names.AddArgument(noName, 'No');

   argName1:= Names.FindOrdinalName(1);
   argName2:= Names.FindOrdinalName(2);

   NEW(disTerm);
   disTerm.Init(argName1);
   disTerm.InitAlternative(argName2);
   Names.DefinePublicName(disName, 'Dis', disTerm);

   Names.AddSystemName(AGRS.failName,'Fail',AGRS.Fail);
   Names.AddSystemName(unifyName, 'Unify', pUnify);
   Names.AddSystemName(equalName, 'Equal', pEqual);
   Names.AddSystemName(lessName, 'Less', pLess);
   Names.AddSystemName(greaterName, 'Greater', pGreater);
   Names.AddSystemName(lessEqName, 'LessEq', pLessEq);
   Names.AddSystemName(grEqName, 'GrEq', pGrEq);
   NEW(AGRS.Failure);
   AGRS.Failure.Init(AGRS.failName);

   Names.AddSystemName(addName, 'Add', pAdd);
   Names.AddSystemName(subName, 'Sub', pSub);
   Names.AddSystemName(mulName, 'Mul', pMul);
   Names.AddSystemName(divName, 'Div', pDiv);
   Names.AddSystemName(modName, 'Mod', pMod);
   Names.AddSystemName(findName, 'Find', pFind);
   Names.AddSystemName(abortName, 'Abort', pAbort);

   NEW(NamesTerm);
   NamesTerm.Init(Names.SystemRoot);
   Names.DefinePublicName(namesName,'Names',NamesTerm);
END Library.
