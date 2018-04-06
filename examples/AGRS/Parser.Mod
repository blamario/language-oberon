MODULE Parser;
IMPORT AGRS,Names,Library,Texts,SYSTEM;


CONST
   MaxStrLength= 60;
   SetBits*= MAX(SET)+1;

TYPE

   ParserProc= PROCEDURE(VAR r:Texts.Reader; l:LONGINT): AGRS.Term;
   ParseWrapper*= POINTER TO RECORD(AGRS.TermDesc)
      handler*: ParserProc;
   END;

VAR
   sentenceName*,spaceCharsName*,customParsersName*,parseName*: AGRS.Name;
   temp,buildingName*,rulesName,varName,blockName,className: AGRS.Name;

   sentenceParser*,attributeParser*,standardParser,customParser: ParseWrapper;
   rulesParser,varParser,blockParser,classParser: ParseWrapper;
   numberParser,stringParser,charParser,charSetParser: ParseWrapper;

   sentence: Texts.Text;         (* Tekst koji se parsira. *)
   spaceChars: Library.CharSet;  (* Delimiteri. *)
   collection: AGRS.ClosedClass; (* CustomParsers znacenje. *)
   idTerm: AGRS.Term;

   attrPosition: INTEGER;    (* Redni broj trenutnog atributa. *)


PROCEDURE Rewind*(VAR rd: Texts.Reader; newPos: LONGINT);
BEGIN
   Texts.OpenReader(rd,sentence,newPos);
END Rewind;


PROCEDURE BackSpace(VAR rd: Texts.Reader);
BEGIN
   Texts.OpenReader(rd,sentence,Texts.Pos(rd)-1);
END BackSpace;


PROCEDURE ParseEmpty*(VAR rd: Texts.Reader; limit: LONGINT): BOOLEAN;
VAR
   ch: CHAR;
BEGIN
   WHILE ~rd.eot & (Texts.Pos(rd)<limit) DO
      Texts.Read(rd,ch);
      IF (rd.elem=NIL) & ~(ORD(ch) MOD SetBits IN 
           spaceChars.value[ORD(ch) DIV SetBits]) THEN
         BackSpace(rd);
         RETURN FALSE
      END;
   END;
   RETURN TRUE
END ParseEmpty;


PROCEDURE ExactParse(parser: ParserProc; VAR rd: Texts.Reader; limit: LONGINT): AGRS.Term;
VAR
   result: AGRS.Term;
BEGIN
   result:= parser(rd,limit);
   IF (result.indirection#AGRS.failName) & ParseEmpty(rd,limit) THEN
      RETURN result
   ELSE
      RETURN AGRS.Failure
   END
END ExactParse;


PROCEDURE ScanCharacter(chSeek: CHAR; 
      VAR rd: Texts.Reader; limit: LONGINT): BOOLEAN;
VAR
   chRead: CHAR;
BEGIN
   WHILE Texts.Pos(rd)<limit DO
      Texts.Read(rd,chRead);
      IF chSeek=chRead THEN
         RETURN TRUE
      END;
   END;
   RETURN FALSE
END ScanCharacter;


PROCEDURE ParseTheCharacter(chExpect: CHAR; 
      VAR rd: Texts.Reader; limit: LONGINT): BOOLEAN;
VAR
   chRead: CHAR;
BEGIN
   IF Texts.Pos(rd)<limit THEN
      Texts.Read(rd,chRead);
      IF chExpect=chRead THEN
         RETURN TRUE
      END;
   END;
   RETURN FALSE
END ParseTheCharacter;


PROCEDURE ParseTheString*(strExpect: ARRAY OF CHAR; 
      VAR rd: Texts.Reader; limit: LONGINT): BOOLEAN;
VAR
   chRead: CHAR;
   i: INTEGER;
BEGIN
   i:= 0;
   WHILE (Texts.Pos(rd)<limit) & (i<LEN(strExpect)) 
                               & (strExpect[i]#0X) DO
      Texts.Read(rd,chRead);
      IF strExpect[i]#chRead THEN
         RETURN FALSE
      END;
      INC(i);
   END;
   RETURN strExpect[i]=0X
END ParseTheString;


PROCEDURE ParseNumber(VAR rd: Texts.Reader; limit: LONGINT): AGRS.Term;
VAR
   ch: CHAR;
   minus: BOOLEAN;
   x: INTEGER;
BEGIN
   Texts.Read(rd,ch);
   IF ch='-' THEN
      minus:= TRUE;
      Texts.Read(rd,ch);
   ELSE
      minus:= FALSE;
      IF ch='+' THEN
         Texts.Read(rd,ch);
      END
   END;
   IF (ch<'0') OR (ch>'9') THEN
      RETURN AGRS.Failure
   END;
   x:= 0;
   WHILE (ch>='0') & (ch<='9') & (Texts.Pos(rd)<=limit) DO
      IF x <= (MAX(INTEGER)-ORD(ch)+ORD('0')) DIV 10 THEN
         x:= 10*x+ORD(ch)-ORD('0');
      END;
      Texts.Read(rd,ch);
   END;
   IF minus THEN
      x:= -x;
   END;
   BackSpace(rd);
   RETURN Library.NewNumber(x)
END ParseNumber;


PROCEDURE ParseChar(VAR rd: Texts.Reader; limit: LONGINT): AGRS.Term;
VAR
   delimiter,chRead: CHAR;
BEGIN
   Texts.Read(rd,delimiter);
   IF delimiter = "'" THEN
      Texts.Read(rd,chRead);
      Texts.Read(rd,delimiter);
      IF (delimiter="'") & (Texts.Pos(rd)<=limit) THEN
         RETURN Library.NewChar(chRead)
      END;
   END;
   RETURN AGRS.Failure
END ParseChar;


PROCEDURE ParseCharSet(VAR rd: Texts.Reader; limit: LONGINT): AGRS.Term;
VAR
   ch,second: CHAR;
   s: Library.CharSet;
   complement: BOOLEAN;
BEGIN
   Texts.Read(rd,ch);
   IF ch='~' THEN
      complement:= TRUE;
      Texts.Read(rd,ch);
   ELSE
      complement:= FALSE;
   END;
   IF ch#'{' THEN
      RETURN AGRS.Failure
   END;
   IF ParseEmpty(rd,limit) THEN
      RETURN AGRS.Failure
   END;
   s:= Library.NewCharSet();
   Texts.Read(rd,ch);
   IF ch#'}' THEN
      LOOP
         IF ch='\' THEN
            Texts.Read(rd,ch);
            CASE ch OF 
               |'0': ch:= 0X;
               |'s','S': ch:= ' ';
               |'t','T': ch:= 9X;
               |'n','N':
                  ch:= 0DX;
                  s.Include(0AX);
            ELSE
               RETURN AGRS.Failure;
            END;
         END;
         Texts.Read(rd,second);
         IF second='-' THEN
            Texts.Read(rd,second);
            IF second<ch THEN
               RETURN AGRS.Failure
            END;
            WHILE ch<=second DO
               s.Include(ch);
               ch:= CHR(ORD(ch)+1);
            END;
            Texts.Read(rd,second);
         ELSE
            s.Include(ch);
         END;
         IF second#',' THEN
            IF second='}' THEN
               EXIT
            ELSE
               RETURN AGRS.Failure
            END;
         END;
         IF ParseEmpty(rd,limit) THEN
            RETURN AGRS.Failure
         END;
         Texts.Read(rd,ch);
      END;
   END;
   IF Texts.Pos(rd)>limit THEN
      RETURN AGRS.Failure
   END;
   IF complement THEN
      s.Complement();
   END;
   RETURN s
END ParseCharSet;


PROCEDURE ParseIdentifier*(VAR rd: Texts.Reader; limit: LONGINT): AGRS.Term;
VAR
   wd: AGRS.Name;
   str: ARRAY MaxStrLength OF CHAR;
   ch: CHAR;
   i: INTEGER;
BEGIN
   i:= 0;
   REPEAT
      Texts.Read(rd,ch);
      str[i]:= ch;
      INC(i);
   UNTIL (ch<'0') OR (CAP(ch)>'Z') OR
         ((ch>'9') & (CAP(ch)<'A')) OR (Texts.Pos(rd)>limit);
   IF i=1 THEN
      RETURN AGRS.Failure;
   END;
   BackSpace(rd);
   str[i-1]:= 0X;
   wd:= Names.FindPublicName(str);
   IF wd=NIL THEN
      Names.AddArgument(wd,str);
   END;
   RETURN wd
END ParseIdentifier;
   

PROCEDURE ParseString(VAR rd: Texts.Reader; limit: LONGINT): AGRS.Term;
VAR
   ch,between: CHAR;
   str: ARRAY MaxStrLength OF CHAR;
   length: INTEGER;
BEGIN
   Texts.Read(rd,between);
   IF (between="'") OR (between='"') THEN
      length:= 0;
      Texts.Read(rd,ch);
      WHILE (ch#between) & (ch#0DX) & (length<MaxStrLength)
            & (Texts.Pos(rd)<limit) DO
         str[length]:= ch;
         INC(length);
         Texts.Read(rd,ch);
      END;
      IF ch=between THEN
         str[length]:= 0X;
         RETURN Library.NewString(Names.NewStringCopy(str))
      END;
   END;
   RETURN AGRS.Failure
END ParseString;


PROCEDURE ParseCustom(VAR rd: Texts.Reader; limit: LONGINT): AGRS.Term;
VAR
   id,result: AGRS.Term;
   startPos: LONGINT;
   
   
BEGIN
   startPos:= Texts.Pos(rd);
   id:= ParseIdentifier(rd,limit);
   Rewind(rd,startPos);
   IF id.indirection=AGRS.failName THEN
      RETURN AGRS.Failure
   END;
   sentenceName.Assign(Library.SubText(sentence,startPos,limit));
   idTerm.Init(id);
   result:= customParsersName.Evaluate(idTerm);
   sentenceName.Restore();
   Rewind(rd,limit);
   RETURN result
END ParseCustom;


PROCEDURE ParseSentence(VAR rd: Texts.Reader; limit: LONGINT): AGRS.Term;
VAR
   result: AGRS.Term;
   startPos,endPos: LONGINT;

			PROCEDURE ParseSequence(VAR rd: Texts.Reader; limit: LONGINT): AGRS.Term;
			VAR
         first,rest: AGRS.Term;
         newTerm: AGRS.SubTerm;
         scanner: Texts.Reader;
			BEGIN
			   startPos:= Texts.Pos(rd);
         Rewind(scanner,startPos);
         WHILE ScanCharacter(';',scanner,limit) DO
            Rewind(rd,startPos);
            first:= ParseCustom(rd,Texts.Pos(scanner)-1);
            IF first.indirection#AGRS.failName THEN
               Rewind(rd,Texts.Pos(scanner));
               IF ~ParseEmpty(rd,limit) THEN
                  rest:= ParseSequence(rd,limit);
                  IF rest.indirection#AGRS.failName THEN
                     NEW(newTerm);
                     newTerm.Init(first);
                     newTerm.InitQuery(rest);
                     RETURN newTerm
                  END;
               END;
            END;
         END;
         Rewind(rd,startPos);
         Rewind(scanner,startPos);
         WHILE ScanCharacter(')',scanner,limit) DO
			      endPos:= Texts.Pos(scanner);
         END;
         RETURN ParseSentence(rd,endPos-1);
			END ParseSequence;
BEGIN
   startPos:= Texts.Pos(rd);
   result:= ExactParse(ParseChar,rd,limit);
   IF result.indirection#AGRS.failName THEN
      RETURN result
   END;
   Rewind(rd,startPos);
   result:= ExactParse(ParseString,rd,limit);
   IF result.indirection#AGRS.failName THEN
      RETURN result
   END;
   Rewind(rd,startPos);
   result:= ExactParse(ParseNumber,rd,limit);
   IF result.indirection#AGRS.failName THEN
      RETURN result
   END;
   Rewind(rd,startPos);
   result:= ExactParse(ParseCharSet,rd,limit);
   IF result.indirection#AGRS.failName THEN
      RETURN result
   END;
   Rewind(rd,startPos);
   result:= ParseCustom(rd,limit);
   IF result.indirection#AGRS.failName THEN
      RETURN result
   END;
   IF ParseTheCharacter('(',rd,limit) & ~ParseEmpty(rd,limit) THEN
      result:= ParseSequence(rd,limit);
      IF result.indirection#AGRS.failName THEN
         IF ~ParseEmpty(rd,limit) THEN
            IF ParseTheCharacter(')',rd,limit) THEN
               RETURN result
            END;
         END;
      END;
   END;
   RETURN AGRS.Failure
END ParseSentence;


PROCEDURE ParseAttribute(VAR rd: Texts.Reader; limit: LONGINT): AGRS.Term;
VAR
   startPos: LONGINT;
   id,meaning,built: AGRS.Term;
   newTerm: AGRS.Tree;
   attrPos: INTEGER;
BEGIN
   startPos:= Texts.Pos(rd);
   id:= ParseIdentifier(rd,limit);
   IF (id.indirection#AGRS.failName) & ~ParseEmpty(rd,limit) 
         & ParseTheCharacter('=',rd,limit) & ~ParseEmpty(rd,limit) THEN
      meaning:= ParseSentence(rd,limit);
      IF meaning.indirection=AGRS.failName THEN
         RETURN AGRS.Failure
      END;
   ELSIF attrPosition>0 THEN
      Rewind(rd,startPos);
      IF ParseEmpty(rd,limit) THEN
         RETURN AGRS.Failure
      END;
      attrPos:= attrPosition;         
      meaning:= ParseSentence(rd,limit);
      IF meaning.indirection=AGRS.failName THEN
         RETURN AGRS.Failure
      END;
      id:= Names.FindOrdinalName(attrPos);
   ELSE
      RETURN AGRS.Failure
   END;
   built:= buildingName.indirection;
   WITH built: AGRS.Tree DO
      built.AddProperty(id(AGRS.Name),meaning);
      RETURN built
   ELSE
      NEW(newTerm);
      newTerm.Init(built);
      newTerm.AddProperty(id(AGRS.Name),meaning);
      RETURN newTerm
   END;
END ParseAttribute;


PROCEDURE ParseProperties(VAR rd: Texts.Reader; limit: LONGINT): AGRS.Term;
VAR
   startPos: LONGINT;
   attrPos: INTEGER;
   result: AGRS.Term;
   attributeReader: Texts.Reader;
BEGIN
   startPos:= Texts.Pos(rd);
   IF ParseTheCharacter(')',rd,limit) THEN
      RETURN buildingName.indirection
   END;
   attrPos:= attrPosition+1;
   Rewind(rd,startPos);
   WHILE ScanCharacter(',',rd,limit) DO
      attrPosition:= attrPos;
      Rewind(attributeReader,startPos);
      result:= ParseAttribute(attributeReader,Texts.Pos(rd)-1);
      IF result.indirection#AGRS.failName THEN
         IF ParseEmpty(rd,limit) THEN
            RETURN AGRS.Failure
         END;
         attrPosition:= attrPos;
         buildingName.Assign(result);
         result:= ParseProperties(rd,limit);
         buildingName.Restore();
         IF result.indirection#AGRS.failName THEN
            RETURN result
         END;
      END;
   END;
   Rewind(rd,startPos);
   Rewind(attributeReader,startPos);
   WHILE ScanCharacter(')',rd,limit) DO
      startPos:= Texts.Pos(rd);
   END;
   attrPosition:= attrPos;
   RETURN ParseAttribute(attributeReader,startPos-1)
END ParseProperties;


PROCEDURE ParseStandard(VAR rd: Texts.Reader; limit: LONGINT): AGRS.Term;
VAR
   id,result: AGRS.Term;
   startPos: LONGINT;
   result1: AGRS.SubTerm;
   result2: AGRS.Field;
   result3: AGRS.Tree;
BEGIN
   id:= ParseIdentifier(rd,limit);
   IF id.indirection=AGRS.failName THEN
      RETURN AGRS.Failure
   END;
   IF ParseEmpty(rd,limit) THEN
      RETURN id
   END;
   startPos:= Texts.Pos(rd);
   IF ParseTheCharacter('.',rd,limit) THEN
      result:= ParseStandard(rd,limit);
      IF result.indirection#AGRS.failName THEN
         IF (result IS AGRS.Name) OR (result IS AGRS.Field) THEN
            NEW(result2);
            result2.Init(id);
            result2.InitQuery(result);
            RETURN result2
         ELSE
            NEW(result1);
            result1.Init(id);
            result1.InitQuery(result);
            RETURN result1
         END;
      END;
      RETURN AGRS.Failure
   ELSE
      Rewind(rd,startPos);
      IF ParseTheCharacter('(',rd,limit) THEN
         IF ParseEmpty(rd,limit) THEN
            RETURN AGRS.Failure
         END;
         startPos:= Texts.Pos(rd);
         IF ParseTheCharacter(')',rd,limit) THEN
            NEW(result);
            result.Init(id);
         ELSE
            Rewind(rd,startPos);
            NEW(result3);
            result3.Init(id);
            buildingName.Assign(result3);
            attrPosition:= 0;
            result:= ParseProperties(rd,limit);
            buildingName.Restore();
         END;
         RETURN result
      ELSE
         Rewind(rd,startPos);
         RETURN id
      END;
   END;
END ParseStandard;


PROCEDURE ParseRule(VAR rd: Texts.Reader; limit: LONGINT): AGRS.Term;
VAR
   startPos: LONGINT;
   lhs,rhs,rest: AGRS.Term;
   ruleReader: Texts.Reader;
BEGIN
   startPos:= Texts.Pos(rd);
   WHILE ScanCharacter('=',rd,limit) DO
      Rewind(ruleReader,startPos);
      lhs:= ParseStandard(ruleReader,Texts.Pos(rd)-1);
      IF (lhs.indirection#AGRS.failName)
            & ~ParseEmpty(ruleReader,limit)
            & ParseTheCharacter('=', ruleReader,limit)
            & ~ParseEmpty(ruleReader,limit) THEN
         startPos:= Texts.Pos(ruleReader);
         WHILE ScanCharacter(',',rd,limit) DO
            Rewind(ruleReader,startPos);
            rhs:= ParseSentence(ruleReader,Texts.Pos(rd)-1);
            IF (rhs.indirection#AGRS.failName)
                  & ~ParseEmpty(ruleReader,limit)
                  & ParseTheCharacter(',', ruleReader,limit)
                  & ~ParseEmpty(ruleReader,limit) THEN
               rest:= ParseRule(ruleReader,limit);
               IF rest.indirection#AGRS.failName THEN
                  Rewind(rd,Texts.Pos(ruleReader));
                  RETURN AGRS.MakeAlternative(lhs,rhs) (* ,rest *)
               END;
            END;
         END;
         Rewind(rd,startPos);
         Rewind(ruleReader,startPos);
         WHILE ScanCharacter(')',rd,limit) DO
            startPos:= Texts.Pos(rd);
         END;
         rhs:= ParseSentence(ruleReader,startPos-1);
         IF rhs.indirection=AGRS.failName THEN
            RETURN AGRS.Failure
         END;
         IF lhs IS AGRS.Name THEN
            RETURN rhs
         ELSE
            RETURN AGRS.MakeAlternative(lhs,rhs) (* ,NIL *)
         END;
      END;
   END;
   RETURN AGRS.Failure
END ParseRule;


PROCEDURE ParseRules(VAR rd: Texts.Reader; limit: LONGINT): AGRS.Term;
BEGIN
   IF ParseTheString('RULE',rd,limit) & ~ParseEmpty(rd,limit)
         & ParseTheCharacter('(',rd,limit) & ~ParseEmpty(rd,limit) THEN
      RETURN ParseRule(rd,limit)
   ELSE
      RETURN AGRS.Failure
   END;
END ParseRules;

PROCEDURE ParseVar(VAR rd: Texts.Reader; limit: LONGINT): AGRS.Term;
BEGIN
   IF ParseTheString('VAR',rd,limit) THEN
      RETURN AGRS.Variable
   ELSE
      RETURN AGRS.Failure
   END;
END ParseVar;

PROCEDURE ParseBlock(VAR rd: Texts.Reader; limit: LONGINT): AGRS.Term;
VAR
   startPos: LONGINT;
   rest,id: AGRS.Term;
   vars: AGRS.Tree;
BEGIN
   IF ParseTheString('LOCAL',rd,limit) THEN
      Names.LocalBlock;
(*      Names.LocalNames; *)
      NEW(vars);
      vars.Init(Names.SystemRoot);
      LOOP
         IF ParseEmpty(rd,limit) THEN
            EXIT
         END;
         id:= ParseIdentifier(rd,limit);
         IF (id.indirection=AGRS.failName) OR ParseEmpty(rd,limit) THEN
            EXIT
         END;
         vars.AddProperty(id(AGRS.Name),AGRS.Variable);
         startPos:= Texts.Pos(rd);
         IF ~ParseTheCharacter(',',rd,limit) THEN
            Rewind(rd,startPos);
            IF ParseTheString('IN',rd,limit) & ~ParseEmpty(rd,limit) THEN
(*               Names.EndNames; *)
               rest:= ParseSentence(rd,limit);
               Names.EndBlock;
               IF rest.indirection=AGRS.failName THEN
                  RETURN AGRS.Failure
               ELSE
                  RETURN AGRS.MakeLocalBlock(vars,rest)
               END;
            ELSE
               EXIT
            END;
         END;
      END;
(*      Names.EndNames; *)
      Names.EndBlock;
   END;
   RETURN AGRS.Failure
END ParseBlock;

PROCEDURE ParseClass(VAR rd: Texts.Reader; limit: LONGINT): AGRS.Term;
VAR
   startPos: LONGINT;
   tree: AGRS.Term;
   result,tree1: AGRS.Class;
BEGIN
   startPos:= Texts.Pos(rd);
   IF ParseTheString('CLASS',rd,limit) THEN
      Rewind(rd,startPos);
      tree:= ParseStandard(rd,limit);
      IF tree IS AGRS.Tree THEN
         NEW(result);
         tree1:= SYSTEM.VAL(AGRS.Class,tree);
         result^:= tree1^;
         RETURN result
      END;
   END;
   RETURN AGRS.Failure
END ParseClass;


PROCEDURE pParse;
VAR
   txt,parsed: AGRS.Term;
   sentenceReader: Texts.Reader;
BEGIN
   txt:= sentenceName.Value();
   WITH txt: Library.Text DO
      sentence:= txt.base;
      Texts.OpenReader(sentenceReader,sentence,txt.startOffset);
      IF ~ParseEmpty(sentenceReader,txt.endOffset) THEN
         parsed:= ParseSentence(sentenceReader,txt.endOffset);
         IF parsed.indirection#AGRS.failName THEN
            IF ~AGRS.Continued() THEN
               AGRS.result:= parsed;
            END;
            RETURN
         END;
      END;
      parsed:= Library.NewError(Library.SyntaxError);
      parsed.Reduce;
   ELSE
      parsed:= Library.NewError(Library.NotTextType);
      parsed.Reduce;
   END;
END pParse;


PROCEDURE (t: ParseWrapper) Reduce*;
VAR
   txt,parsed: AGRS.Term;
   rd: Texts.Reader;
BEGIN
   txt:= sentenceName.Value();
   WITH txt: Library.Text DO
      sentence:= txt.base;
      Texts.OpenReader(rd,sentence,txt.startOffset);
      parsed:= ExactParse(t.handler,rd,txt.endOffset);
   ELSE
      parsed:= Library.NewError(Library.NotTextType);
   END;
   IF ~AGRS.Continued() THEN
      AGRS.result:= parsed;
   END;
END Reduce;

BEGIN
(* Inicijalizacija parametara i pomocnih promjenljivih. *)
   spaceChars:= Library.NewCharSet();
   spaceChars.Include(' ');
   spaceChars.Include(0X);
   spaceChars.Include(9X);
   spaceChars.Include(0AX);
   spaceChars.Include(0DX);
   Names.DefinePublicName(spaceCharsName,'SpaceCharacters',spaceChars);

   NEW(idTerm);

   NEW(sentenceParser);
   sentenceParser.Init(Names.SystemRoot);
   sentenceParser.handler:= ParseSentence;
   Names.DefinePublicName(temp,'SentenceParser',sentenceParser);

   NEW(standardParser);
   standardParser.Init(Names.SystemRoot);
   standardParser.handler:= ParseStandard;
   Names.DefinePublicName(temp,'StandardParser',standardParser);

   NEW(customParser);
   customParser.Init(Names.SystemRoot);
   customParser.handler:= ParseCustom;
   Names.DefinePublicName(temp,'CustomParser',customParser);

   NEW(attributeParser);
   attributeParser.Init(Names.SystemRoot);
   attributeParser.handler:= ParseAttribute;
   Names.DefinePublicName(temp,'AttributeParser',customParser);

   NEW(numberParser);
   numberParser.Init(Names.SystemRoot);
   numberParser.handler:= ParseNumber;
   Names.DefinePublicName(temp,'NumberParser',numberParser);

   NEW(stringParser);
   stringParser.Init(Names.SystemRoot);
   stringParser.handler:= ParseString;
   Names.DefinePublicName(temp,'StringParser',stringParser);

   NEW(charParser);
   charParser.Init(Names.SystemRoot);
   charParser.handler:= ParseChar;
   Names.DefinePublicName(temp,'CharParser',charParser);

   NEW(charSetParser);
   charSetParser.Init(Names.SystemRoot);
   charSetParser.handler:= ParseCharSet;
   Names.DefinePublicName(temp,'CharSetParser',charSetParser);

   NEW(rulesParser);
   rulesParser.Init(Names.SystemRoot);
   rulesParser.handler:= ParseRules;
   Names.DefinePublicName(temp,'RuleParser',rulesParser);
   
   NEW(varParser);
   varParser.Init(Names.SystemRoot);
   varParser.handler:= ParseVar;
   Names.DefinePublicName(temp,'VarParser',varParser);
   
   NEW(blockParser);
   blockParser.Init(Names.SystemRoot);
   blockParser.handler:= ParseBlock;
   Names.DefinePublicName(temp,'BlockParser',blockParser);
   
   NEW(classParser);
   classParser.Init(Names.SystemRoot);
   classParser.handler:= ParseClass;
   Names.DefinePublicName(temp,'ClassParser',classParser);

   Names.AddSystemName(parseName,'Parse',pParse);
   Names.AddArgument(sentenceName,'Sentence');
   Names.AddArgument(rulesName,'RULE');
   Names.AddArgument(varName, 'VAR');
   Names.AddArgument(blockName, 'LOCAL');
   Names.AddArgument(className, 'CLASS');
   NEW(collection);
   collection.Init(Names.SystemRoot);
   collection.AddProperty(rulesName,rulesParser);
   collection.AddProperty(varName,varParser);
   collection.AddProperty(blockName,blockParser);
   collection.AddProperty(className,classParser);
   collection.AddProperty(AGRS.otherwise,standardParser);
   Names.DefinePublicName(customParsersName,'CustomParsers',collection);
   NEW(buildingName);
   buildingName.Init(Names.SystemRoot);
END Parser.
