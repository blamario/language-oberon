MODULE Parser2;
IMPORT AGRS,Names,Library,Grammars;

CONST
   MaxStrLength=Grammars.MaxStrLength;
VAR
   sentenceName,sExprName,exprName,atomicName: AGRS.Name;
   treeName,tree1Name,attributesName,attributes1Name,subSentenceName: AGRS.Name;
   attributeName: AGRS.Name;
   sequenceName,qualificationName,fieldName: AGRS.Name;
   disjunctionName: AGRS.Name;
   charName,stringName,numberName: AGRS.Name;
   argNoName,numberToIdName,lhsName,rhsName,dummyName: AGRS.Name;
   customName,customParsersName: AGRS.Name;
   customIdTerm: AGRS.Field;
   collection: AGRS.ClosedClass;
   ruleParser,altBuilder,varParser,blockParser,classParser: AGRS.Name;
   rulesName,varName,blockName,className,guardName: AGRS.Name;
   rulesParser,alternativeName,blockLocalsName,guardParser: AGRS.Name;

PROCEDURE NewDisjunction(alt1,alt2: AGRS.Term): AGRS.Term;
VAR
   newTerm: AGRS.Disjunction;
BEGIN
   NEW(newTerm);
   newTerm.Init(alt1);
   newTerm.InitAlternative(alt2);
   RETURN newTerm
END NewDisjunction;

PROCEDURE NewContinuation(base,cont: AGRS.Term): AGRS.Term;
VAR
   newTerm: AGRS.SubTerm;
BEGIN
   NEW(newTerm);
   newTerm.Init(base);
   newTerm.InitQuery(cont);
   RETURN newTerm
END NewContinuation;

PROCEDURE NewTreeRoot(root: AGRS.Term): AGRS.Tree;
VAR
   newTerm: AGRS.Tree;
BEGIN
   NEW(newTerm);
   newTerm.Init(root);
   RETURN newTerm
END NewTreeRoot;

PROCEDURE NewClassRoot(root: AGRS.Term): AGRS.Tree;
VAR
   newTerm: AGRS.Class;
BEGIN
   NEW(newTerm);
   newTerm.Init(root);
   RETURN newTerm
END NewClassRoot;

PROCEDURE NewTree(base: AGRS.Tree; prop: AGRS.Name; value: AGRS.Term): AGRS.Tree;
BEGIN
   base.AddProperty(prop,value);
   RETURN base
END NewTree;

PROCEDURE NewGrammarTree(root,value: AGRS.Term): AGRS.Tree;
BEGIN
   RETURN NewTree(NewTreeRoot(root),Grammars.grammarName,value)
END NewGrammarTree;

PROCEDURE NewOption(grammar: AGRS.Term): AGRS.Tree;
BEGIN
   RETURN NewGrammarTree(Grammars.optionName,grammar)
END NewOption;

PROCEDURE NewCharTerminal(expect: CHAR): AGRS.Tree;
BEGIN
   RETURN NewGrammarTree(Grammars.charTerminalParser,
         Library.NewChar(expect))
END NewCharTerminal;

PROCEDURE NewStringTerminal(expect: ARRAY OF CHAR): AGRS.Term;
BEGIN
   RETURN NewGrammarTree(Grammars.terminalName,
      NewTree(NewTreeRoot(Grammars.stringParser),
         Grammars.treeName,Library.NewString(Names.NewStringCopy(expect))))
END NewStringTerminal;

PROCEDURE NewAttribute(property: AGRS.Name; grammar: AGRS.Term): AGRS.Term;
VAR
   temp: AGRS.Term;
BEGIN
   NEW(temp);
   temp.Init(property);
   RETURN NewTree(NewGrammarTree(Grammars.attrName,grammar),
      Grammars.propertyName,temp)
END NewAttribute;

PROCEDURE NumberToId;
VAR
   n,newTerm: AGRS.Term;
BEGIN
   n:= argNoName.Value();
   WITH n: Library.Number DO
      NEW(newTerm);
      newTerm.Init(Names.FindOrdinalName(n.value));
      Grammars.propertyName.Assign(newTerm);
      AGRS.Continue;
      Grammars.propertyName.Restore;
   ELSE
      AGRS.Fail;
   END;
END NumberToId;

PROCEDURE ParseChar;
VAR
   chRead,chResult: CHAR;
BEGIN
   Grammars.Read(chRead);
   IF chRead="'" THEN
      Grammars.Read(chResult);
      Grammars.Read(chRead);
      IF chRead="'" THEN
         IF Grammars.treeName.indirection=AGRS.Variable THEN
            Grammars.treeName.Assign(Library.NewChar(chResult));
            AGRS.Continue;
            Grammars.treeName.Restore;
            RETURN
         END;
      END;
   END;
   AGRS.Fail;
END ParseChar;

PROCEDURE ParseString;
VAR
   ch,between: CHAR;
   str: ARRAY MaxStrLength OF CHAR;
   length: INTEGER;
BEGIN
   Grammars.Read(between);
   IF (between="'") OR (between='"') THEN
      length:= 0;
      Grammars.Read(ch);
      WHILE (ch#between) & (ch#0DX) & (length<MaxStrLength) DO
         str[length]:= ch;
         INC(length);
         Grammars.Read(ch);
      END;
      IF ch=between THEN
         str[length]:= 0X;
         IF Grammars.treeName.indirection=AGRS.Variable THEN
            Grammars.treeName.Assign(
                  Library.NewString(Names.NewStringCopy(str)));
            AGRS.Continue;
            Grammars.treeName.Restore;
            RETURN
         END;
      END;
   END;
   AGRS.Fail;
END ParseString;

PROCEDURE ParseNumber;
VAR
   ch: CHAR;
   minus: BOOLEAN;
   x: INTEGER;
   c: AGRS.TermStack;
BEGIN
   Grammars.Read(ch);
   IF ch='-' THEN
      minus:= TRUE;
      Grammars.Read(ch);
   ELSE
      minus:= FALSE;
      IF ch='+' THEN
         Grammars.Read(ch);
      END
   END;
   IF (ch<'0') OR (ch>'9') THEN
      AGRS.Fail;
      RETURN
   END;
   x:= 0;
   WHILE (ch>='0') & (ch<='9') DO
      IF x <= (MAX(INTEGER)-ORD(ch)+ORD('0')) DIV 10 THEN
         x:= 10*x+ORD(ch)-ORD('0');
      END;
      Grammars.Read(ch);
   END;
   IF minus THEN
      x:= -x;
   END;
   Grammars.BackSpace;
   IF Grammars.treeName.indirection=AGRS.Variable THEN
      Grammars.treeName.Assign(Library.NewNumber(x));
      c:= AGRS.continuation;
      AGRS.Continue;
      Grammars.treeName.Restore;
   ELSE
      AGRS.Fail;
   END;
END ParseNumber;

PROCEDURE ParseCustom;
VAR
   id,result: AGRS.Term;
BEGIN
   id:= customIdTerm.Actual();
   IF id.indirection=AGRS.Failure THEN
      AGRS.Fail;
   ELSE
      AGRS.Push(id);
      customParsersName.Reduce;
   END;
END ParseCustom;

PROCEDURE ParseClass;
VAR
   result: AGRS.Class;
   t: AGRS.Term;
BEGIN
   NEW(result);
   result.Init(className);
   Grammars.treeName.Assign(result);
   treeName.Reduce;
   Grammars.treeName.Restore;
   t:= AGRS.result;
END ParseClass;

PROCEDURE BuildAlternative;
BEGIN
   Grammars.treeName.Assign(
      AGRS.MakeAlternative(lhsName.indirection,rhsName.indirection));
   AGRS.Continue;
   Grammars.treeName.Restore;
END BuildAlternative;

BEGIN
   Grammars.DefineParser(charName,'P_CharacterAtom',ParseChar);
   Grammars.DefineParser(stringName,'P_StringAtom',ParseString);
   Grammars.DefineParser(numberName,'P_NumberAtom',ParseNumber);
   Grammars.DefineParser(customName,'P_Custom',ParseCustom);
   Grammars.DefineParser(classParser,'P_ParseCLASS',ParseClass);
   Names.AddSystemName(altBuilder,'P_BuildAlternative',BuildAlternative);

   Names.AddArgument(sentenceName,'P_Sentence');
   Names.AddArgument(sExprName,'P_SExpr');
   Names.AddArgument(exprName,'P_Expr');
   Names.AddArgument(treeName,'P_Tree');
   Names.AddArgument(tree1Name,'P_Tree1');
   Names.AddArgument(attributesName,'P_Attributes');
   Names.AddArgument(attributes1Name,'P_Attributes1');
   Names.AddArgument(subSentenceName,'P_SubSentence');
   Names.AddArgument(attributeName,'P_Attribute');
   Names.AddArgument(disjunctionName,'P_Disjunction');
   Names.AddArgument(sequenceName,'P_Sequence');
   Names.AddArgument(qualificationName,'P_Qualification');
   Names.AddArgument(fieldName,'P_Field');
   Names.AddArgument(argNoName,'P_ArgNo');
   Names.AddSystemName(numberToIdName,'P_NumberToName',NumberToId);
   Names.AddArgument(lhsName,'P_LHS');
   Names.AddArgument(rhsName,'P_RHS');
   Names.AddArgument(alternativeName,'P_Alternative');
   Names.AddArgument(varParser,'P_Var');
   Names.AddArgument(ruleParser,'P_Rule');
   Names.AddArgument(rulesParser,'P_Rules');
   Names.AddArgument(guardParser,'P_Guard');
   Names.AddArgument(rulesName,'RULE');
   Names.AddArgument(varName,'VAR');
   Names.AddArgument(blockName,'LOCAL');
   Names.AddArgument(className,'CLASS');
   Names.AddArgument(guardName,'GUARD');
   Names.AddArgument(customParsersName,'P_CustomParsers');
   Names.AddArgument(dummyName, '#Let');
   Names.AddArgument(blockParser,'P_ParseBLOCK');
   Names.AddArgument(blockLocalsName,'P_BlockLocals');
   sentenceName.Init(NewDisjunction(sExprName,disjunctionName));
   sExprName.Init(NewDisjunction(exprName,sequenceName));
   Names.DefinePublicName(atomicName,'P_Atomic',
      NewDisjunction(
         charName,NewDisjunction(
         stringName,
         numberName)));
   exprName.Init(NewDisjunction(
      atomicName,NewDisjunction(
      customName,NewDisjunction(
      Grammars.nameParser,NewDisjunction(
      qualificationName,NewDisjunction(
      fieldName,
      subSentenceName))))));
   tree1Name.Init(AGRS.MakeLocalBlock(
      NewTree(NewTreeRoot(dummyName),
         argNoName,Library.NewNumber(0)),
      attributesName));
   treeName.Init(NewContinuation(
      Grammars.idParser,NewContinuation(
      NewCharTerminal('('),NewContinuation(
      NewOption(tree1Name),
      NewCharTerminal(')')))));
   attributes1Name.Init(NewContinuation(
      attributeName,
      NewOption(NewContinuation(
         NewCharTerminal(','),
         attributesName))));
   attributesName.Init(AGRS.MakeLocalBlock(
      NewTree(NewTreeRoot(dummyName),
         argNoName,NewTree(
            NewTree(NewTreeRoot(Library.addName.indirection),
               Library.argName1,argNoName),
            Library.argName2,Library.NewNumber(1))),
      attributes1Name));
(*   attributesName.Init(NewTree(
      NewTreeRoot(attributes1Name),
      argNoName,NewTree(
         NewTree(
            NewTreeRoot(Library.addName.indirection),
            Library.argName1,argNoName),
         Library.argName2,Library.NewNumber(1))));
*)
   subSentenceName.Init(NewContinuation(
      NewCharTerminal('('),NewContinuation(
      sentenceName,
      NewCharTerminal(')'))));
   attributeName.Init(NewDisjunction(
      NewGrammarTree(
         Grammars.genericAttrName,NewContinuation(
         NewAttribute(Grammars.propertyName,
            Grammars.nameParser),NewContinuation(
         NewCharTerminal('='),
         NewAttribute(Grammars.valueName,exprName)))),
      NewContinuation(
         numberToIdName,
         NewGrammarTree(Grammars.attrName,exprName))));
   disjunctionName.Init(NewGrammarTree(
      Grammars.disjunctionName,NewContinuation(
      NewAttribute(Library.argName1,sExprName),NewContinuation(
      NewCharTerminal('|'),
      NewAttribute(Library.argName2,sentenceName)))));
   sequenceName.Init(NewGrammarTree(
      Grammars.continuationName,NewContinuation(
      NewAttribute(Library.argName1,exprName),NewContinuation(
      NewCharTerminal(';'),
      NewAttribute(Library.argName2,sExprName)))));
   qualificationName.Init(NewGrammarTree(
      Grammars.continuationName,NewContinuation(
      NewAttribute(Library.argName1,Grammars.nameParser),NewContinuation(
      NewCharTerminal('.'),
      NewAttribute(Library.argName2,NewDisjunction(
         treeName,
         qualificationName))))));
   fieldName.Init(NewGrammarTree(
      Grammars.fieldName,NewContinuation(
      NewAttribute(Library.argName1,Grammars.nameParser),NewContinuation(
      NewCharTerminal('.'),
      NewAttribute(Library.argName2,NewDisjunction(
         Grammars.nameParser,
         fieldName))))));
   blockParser.Init(NewContinuation(
      NewStringTerminal('LOCAL'),
      NewGrammarTree(
         Grammars.blockName,NewContinuation(
            NewTree(
               NewTreeRoot(Names.localName),
               Names.bodyName,blockLocalsName),
            NewAttribute(Grammars.rootName,sentenceName)))));
   blockLocalsName.Init(NewContinuation(
      NewGrammarTree(
         Grammars.genericAttrName,NewContinuation(
         NewAttribute(Grammars.propertyName,
            Grammars.nameParser),
         NewAttribute(Grammars.valueName,
            NewTree(
               NewTreeRoot(dummyName),
               Grammars.treeName,AGRS.Variable)))),
      NewDisjunction(
         NewStringTerminal('IN'),
         NewContinuation(
            NewCharTerminal(','),
            blockLocalsName))));
   varParser.Init(NewContinuation(
      NewStringTerminal('VAR'),
      NewTree(
         NewClassRoot(dummyName),
         Grammars.treeName,AGRS.Variable)));
   ruleParser.Init(NewContinuation(
      NewStringTerminal('RULE'),NewContinuation(
      NewCharTerminal('('),
      rulesParser)));
   rulesParser.Init(NewGrammarTree(
      Grammars.disjunctionName,NewContinuation(
         NewAttribute(Library.argName1,alternativeName),
         NewAttribute(Library.argName2,NewDisjunction(
            NewContinuation(
               NewCharTerminal(')'),
               NewTree(NewClassRoot(Grammars.constructName),
                  Grammars.rootName,AGRS.failName)),
            NewContinuation(
               NewCharTerminal(','),
               rulesParser))))));
   alternativeName.Init(NewContinuation(
      NewTree(NewTreeRoot(dummyName),     (* shall it stay class? *)
         Grammars.treeName,NewClassRoot(dummyName)),NewContinuation(
      NewAttribute(lhsName,treeName),NewContinuation(
      NewCharTerminal('='),NewContinuation(
      NewAttribute(rhsName,sExprName),NewContinuation(
      Grammars.treeName,
      altBuilder))))));
   guardParser.Init(NewContinuation(
      NewStringTerminal('GUARD'),
      NewTree(
         NewClassRoot(dummyName),
         Grammars.treeName,AGRS.GuardTrap)));
   Grammars.grammarName.Init(sentenceName);
   NEW(customIdTerm);
   customIdTerm.Init(Grammars.idParser);
   customIdTerm.InitQuery(Grammars.treeName);
   NEW(collection);
   collection.Init(Names.SystemRoot);
   collection.AddProperty(rulesName,ruleParser);
   collection.AddProperty(varName,varParser);
   collection.AddProperty(blockName,blockParser);
   collection.AddProperty(className,classParser);
   collection.AddProperty(guardName,guardParser);
   collection.AddProperty(AGRS.otherwise,treeName);
   customParsersName.Init(collection);
END Parser2.

