MODULE Main;
IMPORT AGRS,Names,Library,Parser,Speller,Parser2,
   Grammars,Permanence,Oberon,Texts;


VAR
   rd: Texts.Reader;
   wr: Texts.Writer;


PROCEDURE InputText(limit: CHAR): Library.Text;
VAR
   text: Texts.Text;
   ch: CHAR;
   first,last,time: LONGINT;
BEGIN
   text:= Oberon.Par.text;
   Texts.OpenReader(rd,text,Oberon.Par.pos);
   Texts.Read(rd,ch);
   WHILE (ch=' ') OR (ch=9X) DO
      Texts.Read(rd,ch);
   END;
   IF ch='^' THEN
      Oberon.GetSelection(text,first,last,time);
      IF (time=0) OR (text=NIL) THEN
         RETURN NIL
      END;
   ELSE
      first:= Texts.Pos(rd)-1;
      WHILE (ch#limit) & ~rd.eot DO
         Texts.Read(rd,ch);
      END;
      last:= Texts.Pos(rd)-1;
   END;
   RETURN Library.SubText(text,first,last)
END InputText;

PROCEDURE InputValue(): AGRS.Term;
VAR
   textTerm: Library.Text;
   t: AGRS.Term;
BEGIN
   textTerm:= InputText(0DX);
   IF textTerm=NIL THEN
      RETURN NIL
   END;
   Grammars.sentenceName.Assign(textTerm);
   t:= Grammars.parseName.Value();
(*   t:= Names.IsolateSymbols(Parser.parseName); *)
   Grammars.sentenceName.Restore();
(* RETURN t; *)
   RETURN Permanence.environmentName.Evaluate(t)
(*   RETURN t.Value() *)
END InputValue;

   
PROCEDURE Evaluate*;
VAR
   t,s: AGRS.Term;
BEGIN
   t:= InputValue();
   IF t=NIL THEN
      RETURN
   END;
   Speller.thoughtName.Assign(t);
   s:= Speller.spellingName.Value();
   Speller.thoughtName.Restore;
   WITH s: Library.Text DO
      Texts.Save(s.base,s.startOffset,s.endOffset,wr.buf);
   END;
   Texts.WriteLn(wr);
   Texts.Append(Oberon.Log,wr.buf);
END Evaluate;


PROCEDURE AssignDefinition(param: AGRS.Name; VAR meaning: AGRS.Term);
BEGIN
   param.Init(meaning);
END AssignDefinition;


PROCEDURE Define*;
VAR
   textTerm: Library.Text;
   definition: AGRS.Term;
BEGIN
   textTerm:= InputText(';');
   IF textTerm=NIL THEN
      RETURN
   END;
   Parser.sentenceName.Assign(textTerm);
   Parser.buildingName.Assign(Names.SystemRoot);
   definition:= Parser.attributeParser.Value();
   Parser.buildingName.Restore();
   Parser.sentenceName.Restore();
   IF definition.indirection=AGRS.failName THEN
      Texts.WriteString(wr,'Syntax error!');
   ELSE
      definition(AGRS.Tree).ProcessAttributes(AssignDefinition);
      Texts.WriteString(wr,'Assigned.');
   END;
   Texts.WriteLn(wr);
   Texts.Append(Oberon.Log,wr.buf);
END Define;

BEGIN
   Texts.OpenWriter(wr);
END Main.
