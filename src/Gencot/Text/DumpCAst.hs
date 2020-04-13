{-# LANGUAGE PackageImports #-}
module Gencot.Text.DumpCAst where

import Language.C.Data.Ident as LCI hiding (dumpIdent)
import Language.C.Data.Node as LCN
import Language.C.Data.Name (nameId)
import Language.C.Data.Position as LCP
import Language.C.Syntax.AST as LCS
import qualified Language.C.Analysis as LCA

dumpGlobals :: [LCA.DeclEvent] -> [String]
dumpGlobals tcs = concat $ map dumpGlobal tcs

dumpGlobal :: LCA.DeclEvent -> [String]
dumpGlobal (LCA.TagEvent (LCA.CompDef (LCA.CompType sueref knd mems attrs n))) =
    ["TagEv CompDef CompType " ++ (dumpSueref sueref) ++ " " ++ (dumpKnd knd)]
    ++ (indent $ concat $ map dumpMember mems)
    ++ indent [(dumpAttrs attrs), (dumpNodeinfo n)]
dumpGlobal (LCA.TagEvent (LCA.EnumDef (LCA.EnumType sueref enms attrs n))) =
    ["TagEv EnumDef EnumType " ++ (dumpSueref sueref)]
    ++ (indent (map dumpEnum enms))
    ++ indent [(dumpAttrs attrs), (dumpNodeinfo n)]
dumpGlobal (LCA.DeclEvent (LCA.Declaration (LCA.Decl vdecl n))) =
    prepend "DeclEv Declaration Decl " ((dumpVarDecl vdecl) ++ indent [dumpNodeinfo n])
dumpGlobal (LCA.DeclEvent (LCA.FunctionDef (LCA.FunDef vdecl stat n))) =
    prepend "DeclEv FunctionDef FunDef " ((dumpVarDecl vdecl) ++ indent [dumpNodeinfo n])
dumpGlobal (LCA.DeclEvent (LCA.ObjectDef (LCA.ObjDef vdecl init n))) =
    prepend "DeclEv ObjectDef ObjDef " ((dumpVarDecl vdecl) ++ indent [dumpNodeinfo n])
dumpGlobal (LCA.DeclEvent (LCA.EnumeratorDef (LCA.Enumerator idnam expr enmtyp n))) =
    ["DeclEv EnumeratorDef Enumerator " ++ (dumpIdent idnam)] ++ indent [dumpNodeinfo n]
dumpGlobal (LCA.TypeDefEvent (LCA.TypeDef idnam typ attrs n)) = 
    ["TypeDefEv TypeDef " ++ (dumpIdent idnam)] ++ indent ((dumpType typ) ++ [(dumpAttrs attrs), (dumpNodeinfo n)])
dumpGlobal (LCA.ParamEvent _) = 
    ["ParamEv ..."]
dumpGlobal (LCA.LocalEvent _) = 
    ["LocalEv ..."]
dumpGlobal (LCA.AsmEvent _) = 
    ["AsmEv ..."]

indent :: [String] -> [String]
indent [] = []
indent (h:r) = ("  " ++ h) : (indent r)

prepend :: String -> [String] -> [String]
prepend s [] = [s]
prepend s (h : r) = (s++h) : r

dumpSueref :: LCI.SUERef -> String
dumpSueref (LCI.AnonymousRef nam) = "Anon " ++ (show $ nameId nam)
dumpSueref (LCI.NamedRef idnam) = "Named " ++ (dumpIdent idnam)

dumpIdent :: LCI.Ident -> String
dumpIdent (LCI.Ident s i n) = s ++ "(" ++ (dumpNodeinfo n) ++ ")"

dumpKnd :: LCA.CompTyKind -> String
dumpKnd LCA.StructTag = "struct"
dumpKnd LCA.UnionTag = "union"

dumpAttrs :: LCA.Attributes -> String
dumpAttrs [] = "no attrs"
dumpAttrs _ = "attrs"

dumpNodeinfo :: LCN.NodeInfo -> String
dumpNodeinfo (LCN.OnlyPos pos plen) = dumpOnlyPos pos plen 
dumpNodeinfo (LCN.NodeInfo pos plen nam) = "n" ++ (show $ nameId nam) ++ " " ++ (dumpOnlyPos pos plen)

dumpOnlyPos :: LCP.Position -> LCP.PosLength -> String
dumpOnlyPos pos (ps2,len) = (dumpPos pos) ++ (if pos /= ps2 then "-" ++ (dumpPos ps2) else "") ++ "+" ++ (show len) 

dumpPos :: LCP.Position -> String
dumpPos pos | isNoPos pos = "NoPos"
dumpPos pos | isBuiltinPos pos = "Builtin"
dumpPos pos | isInternalPos pos = "Intern"
dumpPos pos = (show (posRow pos)) ++ ":" ++ (show (posColumn pos))

dumpMember :: LCA.MemberDecl -> [String]
dumpMember (LCA.MemberDecl vdecl Nothing n) = (dumpVarDecl vdecl) ++ indent [dumpNodeinfo n]
dumpMember (LCA.MemberDecl vdecl (Just size) n) = prepend "bits " ((dumpVarDecl vdecl) ++ indent [dumpNodeinfo n])
dumpMember (LCA.AnonBitField typ size n) = prepend "bits noname" (indent (dumpType typ))

dumpEnum :: LCA.Enumerator -> String
dumpEnum (LCA.Enumerator idnam expr enmtyp n) = "Enumerator " ++ (dumpIdent idnam)

dumpVarDecl :: LCA.VarDecl -> [String]
dumpVarDecl (LCA.VarDecl vnam dattrs typ) = 
    [(dumpVarName vnam) ++ " (" ++ (dumpDeclAttrs dattrs) ++ ") : "] ++ indent (dumpType typ)

dumpVarName :: LCA.VarName -> String
dumpVarName (LCA.VarName idnam masm) = dumpIdent idnam
dumpVarName LCA.NoName = "noname"

dumpDeclAttrs :: LCA.DeclAttrs -> String
dumpDeclAttrs (LCA.DeclAttrs fattrs stor attrs) = (dumpFunctionAttrs fattrs) ++ (dumpStorage stor) ++ (dumpA attrs)

dumpFunctionAttrs :: LCA.FunctionAttrs -> String
dumpFunctionAttrs fa = (optStr inl "inline") ++ (optStr (inl && nor) " ") ++ (optStr nor "noret") ++ (optStr (inl || nor) " ")
    where inl = LCA.isInline fa
          nor = LCA.isNoreturn fa

dumpStorage :: LCA.Storage -> String
dumpStorage LCA.NoStorage = "noStrg"
dumpStorage (LCA.Auto False) = "auto"
dumpStorage (LCA.Auto True) = "auto<reg>"
dumpStorage (LCA.Static lnk False) = "static<" ++ (dumpLinkage lnk) ++ ">"
dumpStorage (LCA.Static lnk True) = "static<" ++ (dumpLinkage lnk) ++ ",tloc>"
dumpStorage (LCA.FunLinkage lnk) = "func<" ++ (dumpLinkage lnk) ++ ">"

dumpLinkage :: LCA.Linkage -> String
dumpLinkage LCA.NoLinkage = "noLnk"
dumpLinkage LCA.InternalLinkage = "inLnk"
dumpLinkage LCA.ExternalLinkage = "exLnk"

optStr :: Bool -> String -> String
optStr b s = if b then s else ""

dumpType :: LCA.Type -> [String]
dumpType (LCA.DirectType tnam quals attrs) = 
    ["Dir(" ++ (dumpTypeName tnam) ++ " " ++ (dumpQA quals attrs) ++ ")"]
dumpType (LCA.PtrType typ quals attrs) =
    (prepend "Ptr(" (dumpType typ)) ++ (indent [(dumpQA quals attrs) ++ ")"])
dumpType (LCA.ArrayType typ size quals attrs) = 
    (prepend "Arr(" (dumpType typ)) ++ (indent [(dumpQA quals attrs) ++ ")"])
dumpType (LCA.FunctionType (LCA.FunType typ pars var) attrs) = 
    (prepend "Fun(" (dumpType typ)) ++ (indent ((dumpPars pars var) ++ [(dumpA attrs) ++ ")"]))
dumpType (LCA.FunctionType (LCA.FunTypeIncomplete typ) attrs) = 
    (prepend "Fun(" (dumpType typ)) ++ (indent [(dumpA attrs) ++ ")"])
dumpType (LCA.TypeDefType (LCA.TypeDefRef idnam typ n) quals attrs) = 
    ["Ref(" ++ (dumpIdent idnam) ++ (dumpNodeinfo n) ++ " " ++ (dumpQA quals attrs) ++ ")"]

dumpQA quals attrs = (dumpQuals quals) ++ dumpA attrs
dumpA attrs = if null attrs then "" else ";" ++ (dumpAttrs attrs)

dumpTypeName :: LCA.TypeName -> String
dumpTypeName LCA.TyVoid = "void"
dumpTypeName (LCA.TyIntegral it) = show it
dumpTypeName (LCA.TyFloating ft) = show ft
dumpTypeName (LCA.TyComplex ft) = "cmplx " ++ (show ft)
dumpTypeName (LCA.TyComp (LCA.CompTypeRef sueref knd n)) = 
    (dumpKnd knd) ++ " " ++ (dumpSueref sueref) ++ ";" ++ (dumpNodeinfo n)
dumpTypeName (LCA.TyEnum (LCA.EnumTypeRef sueref n)) =
    "enum " ++ (dumpSueref sueref) ++ ";" ++ (dumpNodeinfo n)
dumpTypeName (LCA.TyBuiltin _) = "builtin"

dumpQuals :: LCA.TypeQuals -> String
dumpQuals q = (optStr c "C") ++ (optStr v "V") ++ (optStr r "R") ++ (optStr a "A") ++ (optStr l "L") ++ (optStr n "N")
    where c = LCA.constant q
          v = LCA.volatile q
          r = LCA.restrict q
          a = LCA.atomic q
          l = LCA.nullable q
          n = LCA.nonnull q
    
dumpPars :: [LCA.ParamDecl] -> Bool -> [String]
dumpPars pars var = prepend "(" ((concat $ map dumpPar pars) ++ [if var then "...)" else ")"])

dumpPar :: LCA.ParamDecl -> [String]
dumpPar (LCA.ParamDecl vdecl n) = (dumpVarDecl vdecl) ++ indent [(dumpNodeinfo n)]
dumpPar (LCA.AbstractParamDecl vdecl n) = (dumpVarDecl vdecl) ++ indent [(dumpNodeinfo n)]
