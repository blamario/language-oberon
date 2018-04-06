MODULE Speller;
IMPORT AGRS,Names,Library,Texts,TextFrames;


CONST
   SetBits= MAX(SET)+1;
   TabChar= 9X;
TYPE

   SpellingHandlerType= PROCEDURE(t: AGRS.Term): AGRS.Term;
   SpellingWrapper= POINTER TO RECORD(AGRS.TermDesc)
      handler: SpellingHandlerType;
   END;
VAR
   FindSpelling: SpellingHandlerType;
   spelledTextName,spellingName*,spellingsName*: AGRS.Name;
   thoughtName*,nameSpellingName,indentionName: AGRS.Name;
   standardSpellingName: AGRS.Name;


   sys: SpellingWrapper;
   collection: AGRS.ClosedClass;

   spelled: Texts.Text; (* Akumulira spelovani tekst. *)
   wr: Texts.Writer; 
   firstAttr: BOOLEAN; (* Da li je prvi spelovani atribut ili ne. *)

(* Sljedece je u planu.

   grammarSpellMeanings: AGRS.Class;
   grammarSpellingName: AGRS.Name;

PROCEDURE GrammarTermSpellings(query: AGRS.Term): AGRS.Term;
VAR
   result: AGRS.Term;
BEGIN
   IF query=NIL THEN
      NEW(result);
      result.Init(AGRS.lastName);
   ELSE
      result:= Grammars.grammarsName.Evaluate(query);
      Grammars.grammarName.Assign(result);
      Library.thoughtName.Assign(query);
      result:= grammarSpellingName.Value();
      Library.thoughtName.Restore();
      Grammars.grammarName.Restore();
   END;
   RETURN result
END GrammarTermSpellings;

PROCEDURE GrammarSpelling(): AGRS.Term;
BEGIN
   RETURN grammarSpellMeanings.Evaluate(grammarName);
END GrammarSpelling;
*)


PROCEDURE NewText(): Library.Text;
VAR
   oldLength: LONGINT;
BEGIN
   oldLength:= spelled.len;
   Texts.Append(spelled,wr.buf);
   RETURN Library.SubText(spelled,oldLength,spelled.len)
END NewText;

PROCEDURE pNameSpelling();
VAR
   s: AGRS.Term;
BEGIN
   s:= Library.NewString(Names.NameSpelling(thoughtName.indirection));
   s.Reduce;
END pNameSpelling;



PROCEDURE SpellAttribute(name: AGRS.Name; VAR t: AGRS.Term);
VAR
   nameSpellPtr: Names.CharPtr;
   spelled: Library.Text;
   meaning,indention: AGRS.Term;
   i: INTEGER;
BEGIN
   IF firstAttr THEN
      firstAttr:= FALSE;
   ELSE
      Texts.Write(wr,',');
      Texts.Write(wr,' ');
   END;
   Texts.WriteLn(wr);
   indention:= indentionName.Value();
   IF indention IS Library.Number THEN
      FOR i:= 1 TO indention(Library.Number).value DO
         Texts.Write(wr,TabChar);
      END;
   END;
   nameSpellPtr:= Names.NameSpelling(name);
   Texts.WriteString(wr,nameSpellPtr^);
   Texts.Write(wr,'=');
   spelled:= spelledTextName.indirection(Library.Text);
   spelled.AppendBuffer(wr.buf);
   thoughtName.Assign(t);
   IF (t IS AGRS.SubTerm) & ~(t.indirection IS AGRS.Name) OR
         (t IS AGRS.Disjunction) THEN
      Texts.Write(wr,'(');
      Texts.WriteLn(wr);
      FOR i:= 1 TO indention(Library.Number).value+1 DO
         Texts.Write(wr,TabChar);
      END;
      indentionName.Assign(
            Library.NewNumber(indention(Library.Number).value+1));
      spelled.AppendBuffer(wr.buf);
      meaning:= standardSpellingName.Value();
      indentionName.Restore();
      Texts.Write(wr,')');
      meaning(Library.Text).AppendBuffer(wr.buf);
   ELSE
      meaning:= FindSpelling(t);
   END;
   thoughtName.Restore();
   IF meaning IS Library.Text THEN
      spelled.AppendText(meaning(Library.Text));
   ELSE
      Texts.WriteString(wr,'!@# Unspellable! ');
      spelled.AppendBuffer(wr.buf);
   END;
END SpellAttribute;


PROCEDURE StandardSpelling(query: AGRS.Term): AGRS.Term;
VAR
   result: Library.Text;
   nameSpellPtr: Names.CharPtr;
   rest,indention: AGRS.Term;
   i: INTEGER;
BEGIN
   IF query IS AGRS.SystemTerm THEN
      IF query=AGRS.GuardTrap THEN
         Texts.WriteString(wr,'GUARD');
      ELSE
         Texts.WriteString(wr,'#SYSTEM!');
      END;
      RETURN NewText()
   END;
   indention:= indentionName.Value();
   IF (query IS AGRS.SubTerm) OR (query IS AGRS.Field) OR 
            (query IS AGRS.Disjunction) THEN
      rest:= FindSpelling(query.indirection);
      IF query IS AGRS.Disjunction THEN
         Texts.WriteString(wr,' | ');
         result:= rest(Library.Text);
         rest:= query(AGRS.Disjunction).alternative;
      ELSE
         IF query.indirection IS AGRS.Name THEN
            Texts.Write(wr,'.');
         ELSE
            Texts.Write(wr,';');
            Texts.WriteLn(wr);
            FOR i:= 1 TO indention(Library.Number).value DO
               Texts.Write(wr,TabChar);
            END;
         END;
         result:= rest(Library.Text);
         rest:= query(AGRS.SubTerm).query;
      END;
      result.AppendBuffer(wr.buf);
      rest:= FindSpelling(rest);
      result.AppendText(rest(Library.Text));
      RETURN result
   ELSIF query IS AGRS.Name THEN
      nameSpellPtr:= Names.NameSpelling(query);
      Texts.WriteString(wr,nameSpellPtr^);
      RETURN NewText()
   ELSE
      IF query IS AGRS.Block THEN
         Texts.WriteString(wr,'LOCAL ');
      ELSE
         nameSpellPtr:= Names.NameSpelling(query.indirection);
         Texts.WriteString(wr,nameSpellPtr^);
      END;
      Texts.Write(wr,'(');
      result:= NewText();
      IF query IS AGRS.Tree THEN
         WITH query: AGRS.Tree DO
            spelledTextName.Assign(result);
            firstAttr:= TRUE;
            WITH indention: Library.Number DO
               indentionName.Assign(
                     Library.NewNumber(indention.value+1));
               query.ProcessAttributes(SpellAttribute);
               indentionName.Restore();
            ELSE
               query.ProcessAttributes(SpellAttribute);
            END;
            result:= spelledTextName.indirection(Library.Text);
            spelledTextName.Restore();
         END;
      END;
      Texts.Write(wr,')');
      result(Library.Text).AppendBuffer(wr.buf);
      IF query IS AGRS.Block THEN
         Texts.WriteString(wr,' IN ');
         result(Library.Text).AppendBuffer(wr.buf);
         rest:= FindSpelling(query.indirection);
         result.AppendText(rest(Library.Text));
      END;
      RETURN result
   END;
END StandardSpelling;


PROCEDURE NumberSpelling(query: AGRS.Term): AGRS.Term;
BEGIN
   WITH query: Library.Number DO
      Texts.WriteInt(wr,query.value,0);
      RETURN NewText()
   ELSE
      RETURN AGRS.Failure
   END;
END NumberSpelling;


PROCEDURE CharSpelling(query: AGRS.Term): AGRS.Term;
BEGIN
   WITH query: Library.Character DO
      Texts.Write(wr,"'");
      Texts.Write(wr,query.value);
      Texts.Write(wr,"'");
      RETURN NewText()
   ELSE
      RETURN AGRS.Failure
   END;
END CharSpelling;


PROCEDURE CharSetSpelling(query: AGRS.Term): AGRS.Term;
VAR
   ch: CHAR;
   first: BOOLEAN;
BEGIN
   WITH query: Library.CharSet DO
      ch:= MIN(CHAR);
      Texts.Write(wr,'{');
      first:= TRUE;
      LOOP
         IF ((ch=0DX) & (0AH MOD SetBits IN query.value[0AH DIV SetBits])) THEN
            ch:= CHR(ORD(ch)+1);
         END;
         IF ORD(ch) MOD SetBits IN query.value[ORD(ch) DIV SetBits] THEN
            IF ~first THEN
               Texts.Write(wr,',');
            END;
            first:= FALSE;
            IF (ch<=' ') THEN
               Texts.Write(wr,'\');
               CASE ch OF
                  |9X: Texts.Write(wr,'T');
                  |' ': Texts.Write(wr,'S');
                  |0AX,0DX: Texts.Write(wr,'N');
                  |0X: Texts.Write(wr,'0');
               ELSE
                  Texts.Write(wr,'?');
               END;
            ELSE
               IF (ch=',') OR (ch='}') OR (ch='{') OR (ch='\') THEN
                  Texts.Write(wr,'\');
               END;
               Texts.Write(wr,ch);
               IF (ORD(ch)+1) MOD SetBits IN 
                     query.value[(ORD(ch)+1) DIV SetBits] THEN
                  REPEAT
                     ch:= CHR(ORD(ch)+1);
                  UNTIL ~(ORD(ch) MOD SetBits IN 
                        query.value[ORD(ch) DIV SetBits]);
                  ch:= CHR(ORD(ch)-1);
                  Texts.Write(wr,'-');
                  IF (ch=',') OR (ch='}') OR (ch='{') OR (ch='\') THEN
                     Texts.Write(wr,'\');
                  END;
                  Texts.Write(wr,ch);
               END;
            END;
         END;
         IF ch<MAX(CHAR) THEN
            ch:= CHR(ORD(ch)+1);
         ELSE
            EXIT
         END
      END;
      Texts.Write(wr,'}');
      RETURN NewText()
   ELSE
      RETURN AGRS.Failure
   END;
END CharSetSpelling;


PROCEDURE StringSpelling(query: AGRS.Term): AGRS.Term;
BEGIN
   WITH query: Library.String DO
      Texts.Write(wr,'"');
      Texts.WriteString(wr,query.value^);
      Texts.Write(wr,'"');
      RETURN NewText()
   ELSE
      RETURN AGRS.Failure
   END;
END StringSpelling;
   

PROCEDURE ErrorSpelling(query: AGRS.Term): AGRS.Term;
BEGIN
   WITH query: Library.Error DO
      CASE query.value OF
         Library.NotLogicalType: Texts.WriteString(wr,'Not the logical type!');
         |Library.NotNumberType: Texts.WriteString(wr,'Not the number type!');
         |Library.NotStringType: Texts.WriteString(wr,'Not the string type!');
         |Library.NotCharacterType: Texts.WriteString(wr,'Not the character type!');
         |Library.NotTextType: Texts.WriteString(wr,'Not the text type!');
         |Library.SyntaxError: Texts.WriteString(wr,'Syntax error!');
         |Library.NotFound: Texts.WriteString(wr,'Undefined word meaning!');
      END;
      RETURN NewText()
   ELSE
      RETURN AGRS.Failure
   END;
END ErrorSpelling;

PROCEDURE VarSpelling(query: AGRS.Term): AGRS.Term;
BEGIN
   HALT(255);
   Texts.WriteString(wr,'VAR');
   RETURN NewText()
END VarSpelling;


PROCEDURE TextSpelling(query: AGRS.Term): AGRS.Term;
BEGIN
   RETURN query.Value()
END TextSpelling;


PROCEDURE pSpelling(query: AGRS.Term): AGRS.Term;
VAR
   result: AGRS.Term;
BEGIN
   IF query IS AGRS.Atomic THEN
      thoughtName.Assign(query);
      result:= spellingsName.Evaluate(query);
      thoughtName.Restore;
      RETURN result
   ELSE
      RETURN StandardSpelling(query);
   END;
END pSpelling;


PROCEDURE (t: SpellingWrapper) Reduce;
VAR
   text: AGRS.Term;
BEGIN
   text:= t.handler(thoughtName.indirection);
   text.Reduce;
END Reduce;

PROCEDURE NewSpeller(h: SpellingHandlerType): AGRS.Term;
VAR
   newTerm: SpellingWrapper;
BEGIN
   NEW(newTerm);
   newTerm.Init(Names.SystemRoot);
   newTerm.handler:= h;
   RETURN newTerm
END NewSpeller;

BEGIN

   spelled:= TextFrames.Text("");
   Texts.OpenWriter(wr);
   NEW(spelledTextName);
   spelledTextName.Init(Names.SystemRoot);
   NEW(collection);
   collection.Init(Names.SystemRoot);
   collection.AddProperty(Library.numberName,
              NewSpeller(NumberSpelling));
   collection.AddProperty(Library.stringName,NewSpeller(StringSpelling));
   collection.AddProperty(Library.textName,NewSpeller(TextSpelling));
   collection.AddProperty(Library.charName,NewSpeller(CharSpelling));
   collection.AddProperty(Library.charSetName,NewSpeller(CharSetSpelling));
   collection.AddProperty(Library.errorName,NewSpeller(ErrorSpelling));
   collection.AddProperty(Names.VariableRoot,NewSpeller(VarSpelling));
   Names.DefinePublicName(standardSpellingName,'StandardSpelling',
         NewSpeller(StandardSpelling));
   collection.AddProperty(AGRS.otherwise,standardSpellingName);
   Names.DefinePublicName(spellingsName,'Spellings',collection);
   Names.DefinePublicName(indentionName,'Indention',
         Library.NewNumber(0));
   Names.AddSystemName(nameSpellingName,'NameSpelling',pNameSpelling);
   Names.DefinePublicName(spellingName,'Spelling',
         NewSpeller(pSpelling));
   Names.AddArgument(spelledTextName,'SpelledTree');
   Names.AddArgument(thoughtName,'Thought');
   FindSpelling:= pSpelling;
END Speller.

