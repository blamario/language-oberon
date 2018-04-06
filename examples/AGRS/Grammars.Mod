MODULE Grammars;
IMPORT AGRS, Names, Library, Parser, Texts;

CONST
   SetBits= MAX(SET)+1;
   MaxStrLength*= 30;
TYPE
   ParserProc= PROCEDURE;
   ParserTerm= POINTER TO RECORD(AGRS.TermDesc)
      handler: ParserProc;
   END;
   BuilderTerm= POINTER TO RECORD(AGRS.TermDesc)
      property: AGRS.Name;
   END;
   GenericBuilderTerm= POINTER TO RECORD(AGRS.TermDesc)
   END;
   SetLimitTerm= POINTER TO RECORD(AGRS.TermDesc)
      limit: LONGINT;
   END;
   ReaderProc= PROCEDURE(VAR in: CHAR);
VAR
   Read*: ReaderProc;
   BackSpace*: PROCEDURE;
   input: Texts.Reader;
   inputString: Names.CharPtr;
   inputText: Texts.Text;
   position,limit: LONGINT;
   EmptyMarker: AGRS.Atomic;
   spaceChars,idChars: Library.CharSet;
   i: INTEGER;
   temp: AGRS.SubTerm;
   tempDis: AGRS.Disjunction;
   disjunctionBuilder,continuationBuilder: AGRS.SystemTerm;
   fieldBuilder,blockBuilder: AGRS.SystemTerm;
   nameToTreeBuilder: AGRS.SystemTerm;
   localConsName,classConsName: AGRS.Name;
   grammarName*,followName: AGRS.Name;
   treeName*,propertyName*,valueName*,rootName*: AGRS.Name;
   sentenceName*,genericRootName,emptyName: AGRS.Name;
   spaceCharsName,idCharsName: AGRS.Name;
   genericAttrName*,disjunctionName*,continuationName*: AGRS.Name;
   fieldName*,blockName*: AGRS.Name;
   optionName*: AGRS.Name;
   terminalName*,attrName*,constructName*,parseEndName: AGRS.Name;
   parseName*,defaultGrammarName: AGRS.Name;
   charParser*,stringParser*: AGRS.Name;
   charTerminalParser*,stringTerminalParser*: AGRS.Name;
   spaceParser,nameParser*,idParser*,recurrenceParser: AGRS.Name;

PROCEDURE ReadFile(VAR ch: CHAR);
BEGIN
   REPEAT
      Texts.Read(input, ch);
      INC(position);
   UNTIL input.elem=NIL;
END ReadFile;

PROCEDURE ReadString(VAR ch: CHAR);
BEGIN
   ch:= inputString[position];
   INC(position);
END ReadString;

PROCEDURE BackSpaceFile;
BEGIN
   DEC(position);
   Texts.OpenReader(input,inputText,position);
END BackSpaceFile;

PROCEDURE BackSpaceString;
BEGIN
   DEC(position);
END BackSpaceString;

PROCEDURE SkipSpaces;
VAR
   ch: CHAR;
   spaces: AGRS.Term;
BEGIN
   spaces:= spaceCharsName.Value();
   WITH spaces: Library.CharSet DO
      REPEAT
         Read(ch);
      UNTIL ~(ORD(ch) MOD SetBits IN 
               spaces.value[ORD(ch) DIV SetBits]) OR (position>limit);
      BackSpace;
   END;
END SkipSpaces;

PROCEDURE pSkipSpaces;
BEGIN
   SkipSpaces;
   AGRS.Continue;
END pSkipSpaces;

PROCEDURE ParseConstruct;
VAR
   expect,skeleton: AGRS.Term;
   newTerm: AGRS.Tree;
BEGIN
   expect:= treeName.indirection;
   skeleton:= rootName.indirection;
   IF expect=AGRS.Variable THEN
      NEW(newTerm);
      WITH skeleton: AGRS.Tree DO
         newTerm^:= skeleton^;
      ELSE
         newTerm.Init(skeleton.indirection);
      END;
      treeName.Assign(newTerm);
      AGRS.Continue;
      treeName.Restore;
   ELSIF AGRS.Equal(expect,skeleton) THEN
      AGRS.Continue;
   ELSE
      AGRS.Fail;
   END;
END ParseConstruct;

PROCEDURE ParseGenericSkeleton(builder: AGRS.Term; check: BOOLEAN);
VAR
   skeleton: AGRS.Class;
BEGIN
   IF check & (treeName.indirection#AGRS.Variable) THEN
      AGRS.Fail;
      RETURN
   END;
   AGRS.Push(builder);
   AGRS.Push(treeName);
   NEW(skeleton);
   skeleton.Init(genericRootName);
   treeName.Assign(skeleton);
   grammarName.Reduce;
   treeName.Restore;
END ParseGenericSkeleton;

PROCEDURE ParseDisjunctConstruct;
BEGIN
   ParseGenericSkeleton(disjunctionBuilder,TRUE);
END ParseDisjunctConstruct;

PROCEDURE ParseContinueConstruct;
BEGIN
   ParseGenericSkeleton(continuationBuilder,TRUE);
END ParseContinueConstruct;

PROCEDURE ParseFieldConstruct;
BEGIN
   ParseGenericSkeleton(fieldBuilder,TRUE);
END ParseFieldConstruct;

PROCEDURE ParseBlockConstruct;
BEGIN
   Names.LocalBlock;
   ParseGenericSkeleton(blockBuilder,TRUE);
   Names.EndBlock;
END ParseBlockConstruct;

PROCEDURE ParseGenericAttribute;
VAR
   builder: GenericBuilderTerm;
BEGIN
   NEW(builder);
   builder.Init(treeName.indirection);
   ParseGenericSkeleton(builder,FALSE);
END ParseGenericAttribute;

PROCEDURE LocalConstruct;
VAR
   newTerm: AGRS.Block;
BEGIN
   IF treeName.indirection IS AGRS.Tree THEN
      NEW(newTerm);
      newTerm.Init(treeName.indirection.indirection);
      treeName.Assign(newTerm);
      AGRS.Continue;
      treeName.Restore();
   ELSE
      AGRS.Fail;
   END;
END LocalConstruct;

PROCEDURE ClassConstruct;
VAR
   newTerm: AGRS.Class;
BEGIN
   IF treeName.indirection IS AGRS.Tree THEN
      NEW(newTerm);
      newTerm.Init(treeName.indirection.indirection);
      treeName.Assign(newTerm);
      AGRS.Continue;
      treeName.Restore();
   ELSE
      AGRS.Fail;
   END;
END ClassConstruct;

PROCEDURE ParseAttribute;
VAR
   prop,val: AGRS.Term;
   root: AGRS.Name;
   builder: BuilderTerm;
BEGIN
   prop:= propertyName.indirection;
   IF ~(prop IS AGRS.Name) THEN
      prop:= prop.indirection;
   END;
   WITH prop: AGRS.Name DO
      root:= treeName.indirection.indirection(AGRS.Name);
      root.Assign(AGRS.Variable);
      prop.Assign(EmptyMarker);
      val:= treeName.Evaluate(prop);
      prop.Restore;
      root.Restore;
      IF val=EmptyMarker THEN
         val:= AGRS.Variable;
      END;
      NEW(builder);
      builder.Init(treeName.indirection);
      builder.property:= prop;
      AGRS.Push(builder);
      treeName.Assign(val);
      grammarName.Reduce;
      treeName.Restore;
   END;
END ParseAttribute;

PROCEDURE ParseTerminal;
VAR
   val: AGRS.Term;
   builder: BuilderTerm;
BEGIN
   NEW(builder);
   builder.Init(treeName.indirection);
   builder.property:= NIL;
   AGRS.Push(builder);
   grammarName.Reduce;
END ParseTerminal;

PROCEDURE ParseCharTerminal;
VAR
   chRead: CHAR;
   chTerm: AGRS.Term;
BEGIN
   Read(chRead);
   chTerm:= grammarName.Value();
   IF chRead=chTerm(Library.Character).value THEN
      AGRS.Continue;
   ELSE
      AGRS.Fail;
   END;
END ParseCharTerminal;

PROCEDURE ParseChar;
VAR
   chRead: CHAR;
   chTerm: Library.Character;
BEGIN
   Read(chRead);
   chTerm:= Library.NewChar(chRead);
   AGRS.Unify(treeName,chTerm);
END ParseChar;

PROCEDURE ParseTheStringPrim(termExpect: AGRS.Term);
VAR
   strExpect: Names.CharPtr;
   chRead: CHAR;
   i: INTEGER;
BEGIN
   IF ~(termExpect IS Library.String) THEN
      AGRS.Fail;
      RETURN
   END;
   strExpect:= termExpect(Library.String).value;
   i:= 0;
   WHILE (i<LEN(strExpect^)) & (strExpect[i]#0X) DO
      Read(chRead);
      IF strExpect[i]#chRead THEN
         AGRS.Fail;
         RETURN
      END;
      INC(i);
   END;
   IF strExpect[i]=0X THEN
      AGRS.Continue;
   ELSE
      AGRS.Fail;
   END;
END ParseTheStringPrim;

PROCEDURE ParseTheString;
BEGIN
   ParseTheStringPrim(treeName.Value());
END ParseTheString;

PROCEDURE ParseStringTerminal;
BEGIN
   ParseTheStringPrim(grammarName.Value());
END ParseStringTerminal;

PROCEDURE ParseIdentifier;
VAR
   wd: AGRS.Name;
   str: ARRAY MaxStrLength OF CHAR;
   ch: CHAR;
   i: INTEGER;
   termExpect: AGRS.Term;
BEGIN
   i:= 0;
   REPEAT
      Read(ch);
      str[i]:= ch;
      INC(i);
   UNTIL ~(ORD(ch) MOD SetBits IN 
         idChars.value[ORD(ch) DIV SetBits]);
   IF i=1 THEN
      AGRS.Fail;
      RETURN
   END;
   BackSpace;
   str[i-1]:= 0X;
   wd:= Names.FindPublicName(str);

   termExpect:= treeName.indirection;
   IF termExpect IS AGRS.Tree THEN
      termExpect:= termExpect.indirection;
   END;
   IF termExpect=wd THEN
      AGRS.Continue;
   ELSIF (termExpect=AGRS.Variable) OR 
         (termExpect=AGRS.Undefined) THEN
      IF wd=NIL THEN
         Names.AddArgument(wd,str);
         treeName.Assign(wd);
         AGRS.Continue;
      ELSE
         treeName.Assign(wd);
(*         wd.Assign(AGRS.Undefined); *)
         AGRS.Continue;
(*         wd.Restore; *)
      END;
      treeName.Restore;
   ELSE
      AGRS.Fail;
   END;
END ParseIdentifier;

PROCEDURE NameToTree;
VAR
   newTerm: AGRS.Tree;
BEGIN
   IF treeName.indirection IS AGRS.Name THEN
      NEW(newTerm);
      newTerm.Init(treeName.indirection);
      treeName.Assign(newTerm);
      AGRS.Continue;
      treeName.Restore;
   ELSE
      AGRS.Continue;
   END;
END NameToTree;

PROCEDURE (t: BuilderTerm) Reduce*;
VAR
   newTerm: AGRS.Tree;
   newTerm2: AGRS.Class;
   newTerm3: AGRS.Block;
BEGIN
(*
   IF treeName.indirection=AGRS.Variable THEN
      AGRS.Fail;
      RETURN
   END;
*)
   IF t.property=NIL THEN
      treeName.Assign(t.indirection);
   ELSE
      IF t.indirection IS AGRS.Tree THEN
         IF t.indirection IS AGRS.Class THEN
            NEW(newTerm2);
            newTerm2^:= t.indirection(AGRS.Class)^;
            newTerm:= newTerm2;
         ELSIF t.indirection IS AGRS.Block THEN
            NEW(newTerm3);
            newTerm3^:= t.indirection(AGRS.Block)^;
            newTerm:= newTerm3;
         ELSE
            NEW(newTerm);
            newTerm^:= t.indirection(AGRS.Tree)^;
         END;
      ELSE
         ASSERT(t.indirection IS AGRS.Name);
         newTerm.Init(t.indirection);
      END;
      newTerm.AddProperty(t.property,treeName.indirection);
      treeName.Assign(newTerm);
   END;
   AGRS.Continue;
   treeName.Restore;
END Reduce;

PROCEDURE (t: GenericBuilderTerm) Reduce*;
VAR
   newTerm: AGRS.Tree;
   newTerm2: AGRS.Class;
   newTerm3: AGRS.Block;
   prop: AGRS.Term;
BEGIN
   NEW(newTerm);
   IF t.indirection IS AGRS.Tree THEN
      IF t.indirection IS AGRS.Class THEN
         NEW(newTerm2);
         newTerm2^:= t.indirection(AGRS.Class)^;
         newTerm:= newTerm2;
      ELSIF t.indirection IS AGRS.Block THEN
         NEW(newTerm3);
         newTerm3^:= t.indirection(AGRS.Block)^;
         newTerm:= newTerm3;
      ELSE
         NEW(newTerm);
         newTerm^:= t.indirection(AGRS.Tree)^;
      END;
   ELSE
      ASSERT(t.indirection IS AGRS.Name);
      newTerm.Init(t.indirection);
   END;
   prop:= propertyName.indirection;
   IF ~(prop IS AGRS.Name) THEN
      prop:= prop.indirection;
   END;
   newTerm.AddProperty(prop(AGRS.Name),valueName.indirection);
   treeName.Assign(newTerm);
   AGRS.Continue;
   treeName.Restore;
END Reduce;

PROCEDURE BuildDisjunction;
VAR
   newTerm: AGRS.Disjunction;
BEGIN
   NEW(newTerm);
   newTerm.Init(Library.argName1.indirection);
   newTerm.InitAlternative(Library.argName2.indirection);
   treeName.Assign(newTerm);
   AGRS.Continue;
   treeName.Restore;
END BuildDisjunction;

PROCEDURE BuildContinuation;
VAR
   newTerm: AGRS.SubTerm;
BEGIN
   NEW(newTerm);
   newTerm.Init(Library.argName1.indirection);
   newTerm.InitQuery(Library.argName2.indirection);
   treeName.Assign(newTerm);
   AGRS.Continue;
   treeName.Restore;
END BuildContinuation;

PROCEDURE BuildField;
VAR
   newTerm: AGRS.Field;
BEGIN
   NEW(newTerm);
   newTerm.Init(Library.argName1.indirection);
   newTerm.InitQuery(Library.argName2.indirection);
   treeName.Assign(newTerm);
   AGRS.Continue;
   treeName.Restore;
END BuildField;

PROCEDURE BuildBlock;
VAR
   newTerm: AGRS.Term;
BEGIN
   newTerm:= treeName.indirection;
   newTerm(AGRS.Tree).RemoveProperty(rootName);
   treeName.Assign(AGRS.MakeLocalBlock(newTerm,rootName.indirection));
   AGRS.Continue;
   treeName.Restore;
END BuildBlock;

PROCEDURE (t: SetLimitTerm) Reduce*;
VAR
   oldLimit: LONGINT;
BEGIN
   oldLimit:= limit;
   limit:= t.limit;
   t.indirection.Reduce;
   limit:= oldLimit;
END Reduce;

PROCEDURE ParseRecurrence;
VAR
   oldLimit: LONGINT;
   seeker: Texts.Reader;
   expect: AGRS.Term;
   chExpect,chRead: CHAR;
   newTerm: AGRS.Tree;
   restoreTerm: SetLimitTerm;
BEGIN
   oldLimit:= limit;
   NEW(newTerm);
   expect:= followName.Value();
   IF expect IS Library.Character THEN
      chExpect:= expect(Library.Character).value;
      newTerm.Init(charTerminalParser);
   ELSE
      chExpect:= expect(Library.String).value[0];
      newTerm.Init(stringTerminalParser);
   END;
   IF inputString=NIL THEN
      REPEAT
         DEC(limit);
         Texts.OpenReader(seeker,inputText,limit);
         Texts.Read(seeker,chRead);
      UNTIL (chRead=chExpect) OR (limit<=position);
   ELSE
      REPEAT
         DEC(limit);
         chRead:= inputString[limit];
      UNTIL (chRead=chExpect) OR (limit<=position);
   END;
   IF chRead=chExpect THEN
      newTerm.AddProperty(grammarName,expect);
      NEW(restoreTerm);
      restoreTerm.Init(newTerm);
      restoreTerm.limit:= oldLimit;
      AGRS.Push(restoreTerm);
      grammarName.Reduce;
   ELSE
      AGRS.Fail;
   END;
   limit:= oldLimit;
END ParseRecurrence;

PROCEDURE (t: ParserTerm) Reduce*;
VAR
   oldPos: LONGINT;
   ch: CHAR;
   spaces: AGRS.Term;
BEGIN
   oldPos:= position;
   spaces:= spaceCharsName.Value();
   WITH spaces: Library.CharSet DO
      REPEAT
         Read(ch);
      UNTIL ~(ORD(ch) MOD SetBits IN 
            spaces.value[ORD(ch) DIV SetBits]) 
         OR (position>limit);
      BackSpace;
   END;
   t.handler;
   position:= oldPos;
   IF inputString=NIL THEN
      Texts.OpenReader(input,inputText,oldPos);
   END;
END Reduce;


PROCEDURE pParse;
VAR
   txt,r: AGRS.Term;
BEGIN
   txt:= sentenceName.Value();
   WITH txt: Library.Text DO
      inputText:= txt.base;
      inputString:= NIL;
      position:= txt.startOffset;
      Texts.OpenReader(input,txt.base,txt.startOffset);
      limit:= txt.endOffset;
      Read:= ReadFile;
      BackSpace:= BackSpaceFile;
   ELSE
      WITH txt: Library.String DO
         position:= 0;
         inputString:= txt.value;
         limit:= txt.Length();
         Read:= ReadString;
         BackSpace:= BackSpaceString;
      END;
   END;
   treeName.Assign(AGRS.Variable);
   r:= grammarName.Evaluate(parseEndName);
   treeName.Restore;
   IF r.indirection#AGRS.failName THEN
      IF ~AGRS.Continued() THEN
         AGRS.result:= r.indirection;
      END;
      RETURN
   END;
   r:= Library.NewError(Library.SyntaxError);
   r.Reduce;
END pParse;

PROCEDURE ExtractTree;
VAR
   newTerm: AGRS.Term;
BEGIN
   SkipSpaces;
   IF position<limit THEN
      AGRS.Fail;
   ELSE
      AGRS.Continue;
      NEW(newTerm);
      newTerm.Init(treeName.indirection);
      AGRS.result:= newTerm;
   END;
END ExtractTree;

PROCEDURE ParseByDefault;
VAR
   r: AGRS.Term;
BEGIN
   Parser.sentenceName.Assign(sentenceName.indirection);
   r:= Parser.parseName.Value();
   Parser.sentenceName.Restore;
   treeName.Assign(r);
   AGRS.Continue;
   treeName.Restore;
END ParseByDefault;

PROCEDURE DefineParser*(VAR parserName: AGRS.Name; 
                    spelling: ARRAY OF CHAR; handlerProc: ParserProc);
VAR
   parser: ParserTerm;
BEGIN
   NEW(parser);
   parser.Init(Names.SystemRoot);
   parser.handler:= handlerProc;
   Names.DefinePublicName(parserName,spelling,parser);
END DefineParser;

BEGIN
   Names.AddArgument(rootName, 'Root');
   Names.AddArgument(treeName, 'Tree');
   Names.AddArgument(propertyName, 'Property');
   Names.AddArgument(grammarName, 'Grammar');
   Names.AddArgument(followName, 'Follow');
   Names.AddArgument(genericRootName, 'GenericRoot');
   Names.AddArgument(valueName, 'Value');
   Names.AddArgument(sentenceName, 'TextSentence');
   Names.AddSystemName(emptyName,'Empty',AGRS.AtomicHandler);
   Names.AddSystemName(defaultGrammarName,'DefaultGrammar',ParseByDefault);
   grammarName.Init(defaultGrammarName);
   Names.AddSystemName(attrName,'Attr',ParseAttribute);
   Names.AddSystemName(genericAttrName,'Attribute',ParseGenericAttribute);
   Names.AddSystemName(constructName,'Construct',ParseConstruct);
   Names.AddSystemName(disjunctionName,'Disjunction',
      ParseDisjunctConstruct);
   Names.AddSystemName(continuationName,'Continuation',
      ParseContinueConstruct);
   Names.AddSystemName(fieldName,'FieldConstruct',ParseFieldConstruct);
   Names.AddSystemName(blockName,'BlockConstruct',ParseBlockConstruct);
   Names.AddSystemName(localConsName,'LocalConstruct',LocalConstruct);
   Names.AddSystemName(classConsName,'ClassConstruct',ClassConstruct);
   Names.AddSystemName(parseEndName,'ParseEnding',ExtractTree);
   Names.AddSystemName(terminalName,'Terminal',ParseTerminal);
   NEW(EmptyMarker);
   EmptyMarker.Init(emptyName);
   DefineParser(charParser,'CharGrammar',ParseChar);
   DefineParser(stringParser,'StringGrammar',ParseTheString);
   DefineParser(charTerminalParser,'CharTerminal',ParseCharTerminal);
   DefineParser(stringTerminalParser,'StringTerminal',ParseStringTerminal);
   DefineParser(nameParser,'NameGrammar',ParseIdentifier);
   DefineParser(spaceParser,'SpaceGrammar',pSkipSpaces);
   DefineParser(recurrenceParser,'Recurrence',ParseRecurrence);
   Names.AddSystemName(parseName,'GrammarParser',pParse);
   NEW(disjunctionBuilder);
   disjunctionBuilder.Init(Names.SystemRoot);
   disjunctionBuilder.InitHandler(BuildDisjunction);
   NEW(continuationBuilder);
   continuationBuilder.Init(Names.SystemRoot);
   continuationBuilder.InitHandler(BuildContinuation);
   NEW(fieldBuilder);
   fieldBuilder.Init(Names.SystemRoot);
   fieldBuilder.InitHandler(BuildField);
   NEW(blockBuilder);
   blockBuilder.Init(Names.SystemRoot);
   blockBuilder.InitHandler(BuildBlock);
   NEW(nameToTreeBuilder);
   nameToTreeBuilder.Init(Names.SystemRoot);
   nameToTreeBuilder.InitHandler(NameToTree);
   NEW(temp);
   temp.Init(nameParser);
   temp.InitQuery(nameToTreeBuilder);
   Names.DefinePublicName(idParser,'IdentifierGrammar',temp);
   NEW(tempDis);
   tempDis.Init(grammarName);
   tempDis.InitAlternative(AGRS.Undefined);
   Names.DefinePublicName(optionName,'Option',tempDis);
   spaceChars:= Library.NewCharSet();
   spaceChars.Include(' ');
   spaceChars.Include(0X);
   spaceChars.Include(9X);
   spaceChars.Include(0AX);
   spaceChars.Include(0DX);
   Names.DefinePublicName(spaceCharsName,'SpaceChars',spaceChars);
   idChars:= Library.NewCharSet();
   FOR i:= ORD('a') TO ORD('z') DO
      idChars.Include(CHR(i));
      idChars.Include(CAP(CHR(i)));
   END;
   FOR i:= ORD('0') TO ORD('9') DO
      idChars.Include(CHR(i));
   END;
   idChars.Include('_');
   Names.DefinePublicName(idCharsName,'IdentifierChars',idChars);
END Grammars.

