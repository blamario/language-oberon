MODULE Names;
IMPORT AGRS,SYSTEM;


CONST
   MaxEntries=64;             (* Broj ulaza u hash tabeli *)
   LastEntry=MaxEntries-1;
TYPE
   CharPtr*= POINTER TO ARRAY OF CHAR;
   PublicName= POINTER TO RECORD(AGRS.NameDesc)    (* Imenovani parametar *)
      spelling: CharPtr;
      next: PublicName;
   END;
   OrdinalName= POINTER TO RECORD(AGRS.NameDesc)   (* Genericki parametar sa imenom 'nth' *)
      number: INTEGER;
      next: OrdinalName;
   END;
   Dictionary= POINTER TO DictRec;     (* Tabela simbola *)
   DictRec= RECORD
      entries: ARRAY MaxEntries OF PublicName;
      next: Dictionary;
   END;
VAR
   top: Dictionary;
   ordinalList: OrdinalName;

   SystemRoot*,VariableRoot*: AGRS.Name;
   localName*, bodyName*: AGRS.Name;

   UndefinedTerm: AGRS.SystemTerm;

   temp: AGRS.Term;
   temp1: AGRS.SubTerm;
   temp2: AGRS.SystemTerm;
   
   systemSpelling: CharPtr;
   systemHash: INTEGER;

   i: INTEGER;
   search: BOOLEAN;



PROCEDURE IsolateSymbols*(query: AGRS.Term): AGRS.Term;
VAR
   d: Dictionary;
   i: INTEGER;
   result: AGRS.Term;
BEGIN
   NEW(d);
   FOR i:= 0 TO LastEntry DO
      d.entries[i]:=top.entries[i];
   END;
   d.next:= top;
   top:= d;
   result:= query.Value();
   top:= top.next;
   RETURN result
END IsolateSymbols;


PROCEDURE LocalBlock*;
VAR
   d: Dictionary;
   i: INTEGER;
BEGIN
   NEW(d);
   FOR i:= 0 TO LastEntry DO
      d.entries[i]:=top.entries[i];
   END;
   d.next:= top;
   top:= d;
END LocalBlock;

PROCEDURE EndBlock*;
BEGIN
   top:= top.next;
END EndBlock;

PROCEDURE LocalNames;
BEGIN
   search:= FALSE;
   bodyName.Reduce;
END LocalNames;

PROCEDURE EndLocalNames;
BEGIN
   search:= TRUE;
   AGRS.Continue;
END EndLocalNames;


PROCEDURE NewStringCopy*(str: ARRAY OF CHAR): CharPtr;
VAR
   result: CharPtr;
   i,length: INTEGER;
BEGIN
   length:= 0;
   WHILE (length#LEN(str)) & (str[length]#0X) DO
      INC(length);
   END;
   NEW(result,length+1);
   FOR i:= 0 TO length-1 DO
      result[i]:= str[i];
   END;
   result[length]:= 0X;
   AGRS.eldestAsked:= AGRS.Fixed;
   RETURN result;
END NewStringCopy;



PROCEDURE HashString(VAR str: ARRAY OF CHAR; module: INTEGER): INTEGER;
VAR
   i,result: INTEGER;
BEGIN
   i:= 0;
   result:= 0;
   WHILE (i<LEN(str)) & (str[i]#0X) DO
      result:= result+ORD(CAP(str[i]));
      INC(i);
   END;
   RETURN result MOD module;
END HashString;


PROCEDURE DefinePublicName*(VAR result: AGRS.Name; spelling: ARRAY OF CHAR; meaning: AGRS.Term);
VAR
   newName: PublicName;
   hash: INTEGER;
   spellingCopy: CharPtr;
BEGIN
   spellingCopy:= NewStringCopy(spelling);
   NEW(newName);
   result:= newName;
   IF meaning#UndefinedTerm THEN
      newName.Init(meaning);
      newName.spelling:= spellingCopy;
      newName.next:= top.entries[systemHash];
      meaning:= newName;
      top.entries[systemHash]:= newName;
      NEW(newName);
   END;
   hash:= HashString(spelling,MaxEntries);
   newName.Init(meaning);
   newName.spelling:= NewStringCopy(spelling);
   newName.next:= top.entries[hash];
   top.entries[hash]:= newName;
END DefinePublicName;

PROCEDURE AddSystemName*(VAR result: AGRS.Name; spelling: ARRAY OF CHAR; handler: AGRS.HandlerType);
VAR
   newTerm: AGRS.SystemTerm;
BEGIN
   NEW(newTerm);
   newTerm.Init(SystemRoot);
   newTerm.InitHandler(handler);
   DefinePublicName(result,spelling,newTerm);
END AddSystemName;


PROCEDURE AddArgument*(VAR result: AGRS.Name; spelling: ARRAY OF CHAR);
BEGIN
   DefinePublicName(result,spelling,UndefinedTerm);
END AddArgument;


PROCEDURE AddAtom*(VAR name: AGRS.Name; spelling: ARRAY OF CHAR): AGRS.Term;
VAR
   newTerm: AGRS.Atomic;
BEGIN
   AddSystemName(name,spelling,AGRS.AtomicHandler);
   NEW(newTerm);
   newTerm.Init(name);
   RETURN newTerm
END AddAtom;


PROCEDURE FindOrdinalName*(ordinalNumber: INTEGER): AGRS.Name;
VAR
   newName,seek,follow: OrdinalName;
BEGIN
   seek:= ordinalList;
   WHILE (seek#NIL) & (seek.number<ordinalNumber) DO
      follow:= seek;
      seek:= seek.next;
   END;
   IF (seek=NIL) OR (seek.number>ordinalNumber) THEN
      NEW(newName);
      newName.Init(UndefinedTerm);
      newName.number:= ordinalNumber;
      newName.next:= seek;
      follow.next:= newName;
      RETURN newName
   ELSE
      RETURN seek
   END;
END FindOrdinalName;


PROCEDURE FindPublicName*(wd: ARRAY OF CHAR): AGRS.Name;
VAR
   follow: PublicName;
   letter: INTEGER;
   ordinal: INTEGER;
BEGIN
   IF ~search THEN
      RETURN NIL
   END;
   follow:= top.entries[HashString(wd,MaxEntries)];
   WHILE follow#NIL DO
      IF follow.spelling[0]=wd[0] THEN
         letter:=1;
         WHILE (wd[letter]=follow.spelling[letter]) & (follow.spelling[letter]#0X) DO
            INC(letter);
         END;
         IF wd[letter]=follow.spelling[letter] THEN
            RETURN follow
         END;
      END;
      follow:=follow.next;
   END;
   letter:= 0;
   ordinal:= 0;
   WHILE (wd[letter]>='0') & (wd[letter]<='9') DO
      ordinal:= 10*ordinal+ORD(wd[letter])-ORD('0');
      INC(letter);
   END;
   IF (ordinal=0) OR (wd[letter+2]#0X) THEN
      RETURN NIL
   END;
   CASE wd[letter-1] OF
      |'1': IF (wd[letter]#'s') OR (wd[letter+1]#'t') THEN RETURN NIL END;
      |'2': IF (wd[letter]#'n') OR (wd[letter+1]#'d') THEN RETURN NIL END;
      |'3': IF (wd[letter]#'r') OR (wd[letter+1]#'d') THEN RETURN NIL END;
   ELSE
      IF (wd[letter]#'t') OR (wd[letter+1]#'h') THEN RETURN NIL END;
   END;
   RETURN FindOrdinalName(ordinal)
END FindPublicName;


PROCEDURE FindPublicNameNoCase*(wd: ARRAY OF CHAR): AGRS.Name;
VAR
   follow: PublicName;
   letter: LONGINT;
BEGIN
   letter:= 0;
   WHILE (wd[letter]#0X) & (letter<LEN(wd)) DO
      wd[letter]:= CAP(wd[letter]);
      INC(letter);
   END;
   follow:=top.entries[HashString(wd,MaxEntries)];
   WHILE follow#NIL DO
      IF CAP(follow.spelling[0])=wd[0] THEN
         letter:=1;
         WHILE (wd[letter]=CAP(follow.spelling[letter])) & (follow.spelling[letter]#0X) DO
            INC(letter);
         END;
         IF wd[letter]=follow.spelling[letter] THEN
            RETURN follow
         END;
      END;
      follow:=follow.next
   END;
   RETURN NIL
END FindPublicNameNoCase;


PROCEDURE NameSpelling*(t: AGRS.Term): CharPtr;
VAR
   nameSpelling: CharPtr;
   size,rest: INTEGER;
   addr: LONGINT;
BEGIN
   WITH t: PublicName DO
      RETURN t.spelling
   ELSE
      WITH t: OrdinalName DO
         size:= 3;
         rest:= t.number;
         REPEAT
            rest:= rest DIV 10;
            INC(size);
         UNTIL rest=0;
         NEW(nameSpelling,size);
         nameSpelling[size-1]:= 0X;
         rest:= t.number;
         IF (rest DIV 10) MOD 10 = 1 THEN
            nameSpelling[size-3]:= 't';
            nameSpelling[size-2]:= 'h';
         ELSE
            CASE rest MOD 10 OF
               |1:
                  nameSpelling[size-3]:= 's';
                  nameSpelling[size-2]:= 't';
               |2:
                  nameSpelling[size-3]:= 'n';
                  nameSpelling[size-2]:= 'd';
               |3:
                  nameSpelling[size-3]:= 'r';
                  nameSpelling[size-2]:= 'd';
               ELSE
                  nameSpelling[size-3]:= 't';
                  nameSpelling[size-2]:= 'h';
            END;
         END;
         size:= size-4;
         REPEAT
            nameSpelling[size]:= CHR(ORD('0') + rest MOD 10);
            rest:= rest DIV 10;
            DEC(size);
         UNTIL size<0;
         RETURN nameSpelling
      ELSE
         IF t IS AGRS.Name THEN
            NEW(nameSpelling,12);
            nameSpelling[0]:= '_';
            size:= 1;
            addr:= SYSTEM.VAL(LONGINT,t);
            REPEAT
               nameSpelling[size]:= CHR(ORD('0') + addr MOD 10);
               addr:= addr DIV 10;
               INC(size);
            UNTIL addr=0;
            nameSpelling[size]:= 0X;
            RETURN nameSpelling;
         END;
         RETURN NewStringCopy('!@#')
      END;
   END;
END NameSpelling;

BEGIN
   search:= TRUE;
   NEW(top);
   top.next:= NIL;
   FOR i:= 0 TO LastEntry DO
      top.entries[i]:= NIL
   END;
   NEW(UndefinedTerm);
   AddArgument(SystemRoot,'#System#');
   UndefinedTerm.Init(SystemRoot);
   UndefinedTerm.InitHandler(AGRS.Continue);
   AddArgument(VariableRoot,'#System#');
   AGRS.Variable.Init(VariableRoot);
   AGRS.Variable.InitHandler(AGRS.Continue);
   NEW(ordinalList);
   ordinalList.Init(UndefinedTerm);
   ordinalList.number:= 1;
   ordinalList.next:= NIL;
   AddArgument(AGRS.otherwise,'Otherwise');
   AddArgument(bodyName, 'LocalBody');
   NEW(temp1);
   NEW(temp2);
   temp1.Init(bodyName);
   temp1.InitQuery(temp2);
   temp2.Init(SystemRoot);
   temp2.InitHandler(EndLocalNames);
   temp:= temp1;
   NEW(temp1);
   NEW(temp2);
   temp2.Init(SystemRoot);
   temp2.InitHandler(LocalNames);
   temp1.Init(temp2);
   temp1.InitQuery(temp);
   DefinePublicName(localName,'LocalNames',temp);
   systemSpelling:= NewStringCopy('#');
   systemHash:= HashString(systemSpelling^, MaxEntries);
END Names.

