MODULE Permanence;
IMPORT AGRS,Names,Library,Parser,Texts,Directories,Grammars;

CONST
   PathDelimiter= '\';
   MaxPathLength= 200;

TYPE
   Term= AGRS.Term;
   FilePrimitive= POINTER TO FilePrimitiveDesc;
   FilePrimitiveDesc= RECORD(AGRS.SubTermDesc)
   END;
   FolderPrimitive= POINTER TO RECORD(FilePrimitiveDesc)
   END;
VAR
   folderRoot, directoryName, extensionName: AGRS.Name;
   environmentName*: AGRS.Name;
   directory: AGRS.Class;
   dirTerm, currentFolder: AGRS.Term;
   i,length: INTEGER;

(*
PROCEDURE Position(t: AGRS.Var; VAR file: Files.File; VAR startPos,endPos: LONGINT);
PROCEDURE Replace(t: AGRS.Var; file: File.File; startPos,endPos: LONGINT; VAR replacement: ARRAY OF CHAR);
PROCEDURE WriteText*(t: AGRS.Var; VAR definition: ARRAY OF CHAR);
PROCEDURE ReadBuffer*(t: AGRS.Var; VAR definition: ARRAY OF CHAR; startPos: LONGINT);
PROCEDURE ReadText*(t: AGRS.Var): CharPtr;
PROCEDURE WriteTerm*(t: AGRS.Var; definition: AGRS.Term);
PROCEDURE WriteDefinition*(t: AGRS.Var);
PROCEDURE Definition*(t: AGRS.Var): AGRS.Term;

PROCEDURE WriteHandler;
VAR
   path: AGRS.SubTerm;
BEGIN
   path:= AGRS.EnvironmentPath(directoryName);
   WriteDefinition(path);
   RETURN Library.doneName
END WriteHandler;
*)

PROCEDURE CorrectExtension(VAR filename: ARRAY OF CHAR): BOOLEAN;
VAR
   extension: AGRS.Term;
   suffix: Names.CharPtr;
   pos1,pos2: INTEGER;
BEGIN
   extension:= extensionName.Value();
   WITH extension: Library.String DO
      suffix:= extension.value;
      pos1:= 0;
      pos2:= 0;
      WHILE filename[pos1]#0X DO
         INC(pos1);
      END;
      WHILE suffix[pos2]#0X DO
         INC(pos2);
      END;
      ASSERT(pos2>3);
      WHILE (filename[pos1]=suffix[pos2]) & (pos1>0) & (pos2>0) DO
         DEC(pos1);
         DEC(pos2);
      END;
      IF (pos2=0) & (filename[pos1]=suffix[pos2]) THEN
         filename[pos1]:= 0X;
         RETURN TRUE
      END;
   END;
   RETURN FALSE
END CorrectExtension;      

PROCEDURE GetPath(pathTerm: Term; VAR pathString: ARRAY OF CHAR);
VAR
   i,length: INTEGER;
   dir: Names.CharPtr;

   PROCEDURE WritePath(t: Term);
   VAR
      t2: Term;
   BEGIN
      t2:= t;
      WITH t2: FilePrimitive DO
         WritePath(t2.indirection);
         WritePath(t2.query);
      ELSE
         dir:= Names.NameSpelling(t(AGRS.Name));
         i:= 0;
         WHILE dir[i]#0X DO
            pathString[length]:= dir[i];
            INC(length);
            INC(i);
         END;
         pathString[length]:= PathDelimiter;
         INC(length);
      END;
   END WritePath;
BEGIN
   length:= 0;
   WritePath(pathTerm);
   pathString[length-1]:= 0X;
END GetPath;
      
PROCEDURE InitFile(dir: Directories.Directory; filename: ARRAY OF CHAR;
                  isDir: BOOLEAN; VAR cont: BOOLEAN);
VAR
   def: AGRS.Name;
   newTerm1: FolderPrimitive;
   newTerm: FilePrimitive;
BEGIN
   cont:= TRUE;
   IF isDir THEN
      IF filename[0]='.' THEN
         RETURN
      END;
      NEW(newTerm1);
      newTerm:= newTerm1;
   ELSE
      IF ~CorrectExtension(filename) THEN
         RETURN
      END;
      NEW(newTerm);
   END;
   def:= Names.FindPublicNameNoCase(filename);
   IF def=NIL THEN
      Names.AddArgument(def,filename);
   END;
   newTerm.Init(currentFolder);
   newTerm.InitQuery(def);
   directory.AddProperty(def,newTerm);
END InitFile;

PROCEDURE InitFiles(t: AGRS.Term): AGRS.Term;
VAR
   path: ARRAY MaxPathLength OF CHAR;
BEGIN
   currentFolder:= t;
   NEW(directory);
   directory.Init(folderRoot);
   directory.AddProperty(directoryName,t);
   GetPath(t,path);
   Directories.Enumerate(Directories.This(path),InitFile);
   RETURN directory
END InitFiles;

PROCEDURE RefreshFolder(dir,value: AGRS.Term);
BEGIN
   IF dir IS FolderPrimitive THEN
      dir:= dir(FolderPrimitive).query;
   END;      
   dir.indirection(AGRS.Class).
       AddProperty(AGRS.lastResult(AGRS.Name),value);
END RefreshFolder;

PROCEDURE (t: FolderPrimitive) Reduce*;
VAR
   newDir: Term;
BEGIN
   newDir:= InitFiles(t);
   RefreshFolder(t.indirection,newDir);
   t.query(AGRS.Name).Assign(newDir);
   newDir.Reduce;
   t.query(AGRS.Name).Restore;
END Reduce;

PROCEDURE (t: FilePrimitive) Reduce*;
VAR
   f: Texts.Text;
   i,j: INTEGER;
   strPtr: Names.CharPtr;
   filename: ARRAY MaxPathLength OF CHAR;
   result: AGRS.Term;
BEGIN
   GetPath(t,filename);
   j:= 0;
   WHILE filename[j]#0X DO
      INC(j);
   END;
(*
   strPtr:= Names.NameSpelling(AGRS.lastResult(AGRS.Name));
   i:= 0;
   WHILE strPtr[i]#0X DO
      filename[j]:= strPtr[i];
      INC(i);
      INC(j);
   END;
*)
   result:= extensionName.Value();
   WITH result: Library.String DO
      strPtr:= result.value;
      i:= 0;
      WHILE strPtr[i]#0X DO
         filename[j]:= strPtr[i];
         INC(i);
         INC(j);
      END;
   END;
   filename[j]:= 0X;
   NEW(f);
   Texts.Open(f,filename);
   Grammars.sentenceName.Assign(Library.SubText(f,0,f.len));
   result:= Grammars.parseName.Value();
   Grammars.sentenceName.Restore();
   RefreshFolder(t.indirection,result);
   result.Reduce;
END Reduce;

BEGIN
   Names.AddArgument(folderRoot, 'FolderClass');
   Names.AddArgument(directoryName, 'Directory');
   Names.AddArgument(extensionName, 'FileExtension');
   Names.AddArgument(environmentName, 'Env');
   extensionName.Init(Library.NewString(Names.NewStringCopy('.ATG')));
   environmentName.Init(InitFiles(environmentName));
END Permanence.

