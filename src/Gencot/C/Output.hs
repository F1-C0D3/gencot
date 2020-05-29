{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Gencot.C.Output where

import Data.Char (isAlphaNum,
                  isLower)
import Data.Maybe (isJust)

import Gencot.Origin (Origin(..),fstLine,lstLine)
import Gencot.C.Ast

import Text.PrettyPrint.Mainland
import Text.PrettyPrint.Mainland.Class

showTopLevels :: [Definition] -> String
showTopLevels defs = pretty 2000 $ pprList defs

addOrig :: Origin -> Doc -> Doc
addOrig (Origin sn en) doc =
    mark "#ORIGIN" sn fstLine
    <> doc <> 
    mark "#ENDORIG" en lstLine
    where mark marker ons line = 
              if null ons then empty 
                          else (hardline <> text marker <+> cont ons line <> hardline)
          cont ons line = (int . line . fst . head) ons <> text (if snd $ head ons then " +" else "")
          hardline = nesting (\i -> text ("\n" ++ replicate i ' '))

pprCommented :: Stm -> Doc
pprCommented (Block items orig) =
    addOrig orig $
    emcomment $ loop items
    where
        emcomment [] = lbrace <> char '-' <+> char '-' <> rbrace
        emcomment ds = lbrace <> char '-' <>
             nest 4 (line <> stack ds) </>
             char '-' <> rbrace
        loop :: [BlockItem] -> [Doc]
        loop [] =
            []
        loop [item] =
            [ppr item]
        loop (item1@(BlockDecl _) : item2@(BlockStm _) : items) =
            (ppr item1 <> line) : loop (item2 : items)
        loop (item1@(BlockStm _) : item2@(BlockDecl _) : items) =
            (ppr item1 <> line) : loop (item2 : items)
        loop (item : items) =
            ppr item : loop items
pprCommented s = lbrace <> char '-' <+> ppr s <+> char '-' <> rbrace

nst = nest 2

nparens :: Doc -> Doc
nparens = enclose lparen rparen . nst

nparensIf :: Bool -> Doc -> Doc
nparensIf True doc  = nparens doc
nparensIf False doc = doc

nbraces :: Doc -> Doc
nbraces = enclose lbrace rbrace . nst

nbrackets :: Doc -> Doc
nbrackets = enclose lbracket rbracket . nst

ncommasep :: [Doc] -> Doc
ncommasep = nst . sep . punctuate comma

nenclosesep :: Doc -> Doc -> Doc -> [Doc] -> Doc
nenclosesep left right p ds =
    case ds of
      [] ->  left <> right
      [d] -> left <> d <> right
      _ ->   left <> nst (sep (punctuate p ds)) <> right

data Fixity = Fixity Assoc Int
  deriving (Eq, Ord)

data Assoc = LeftAssoc | RightAssoc | NonAssoc
  deriving (Eq, Ord)

infix_ :: Int -> Fixity
infix_ = Fixity NonAssoc

infixl_ :: Int -> Fixity
infixl_ = Fixity LeftAssoc

infixr_ :: Int -> Fixity
infixr_ = Fixity RightAssoc

-- | Pretty print infix binary operators
infixop :: (Pretty a, Pretty b, Pretty op, CFixity op)
        => Int -- ^ precedence of context
        -> op  -- ^ operator
        -> a   -- ^ left argument
        -> b   -- ^ right argument
        -> Doc
infixop prec op l r =
    parensOp prec op $
    pprPrec leftPrec l <+> ppr op <+/> pprPrec rightPrec r
  where
    leftPrec | opAssoc == RightAssoc = opPrec + 1
             | otherwise             = opPrec

    rightPrec | opAssoc == LeftAssoc = opPrec + 1
              | otherwise            = opPrec

    Fixity opAssoc opPrec = fixity op

-- | Pretty print prefix unary operators
prefixop :: (Pretty a, Pretty op, CFixity op)
         => Int -- ^ precedence of context
         -> op  -- ^ operator
         -> a   -- ^ argument
         -> Doc
prefixop prec op arg =
    nparensIf (prec > opPrec) $
    ppr op <> pprPrec rightPrec arg
  where
    rightPrec | opAssoc == LeftAssoc = opPrec + 1
              | otherwise            = opPrec

    Fixity opAssoc opPrec = fixity op

parensList :: [Doc] -> Doc
parensList = nenclosesep lparen rparen comma

bracesList :: [Doc] -> Doc
bracesList = nenclosesep lbrace rbrace comma

bracesSemiList :: [Doc] -> Doc
bracesSemiList = nenclosesep lbrace rbrace semi

embrace :: [Doc] -> Doc
embrace [] = lbrace <+> rbrace
embrace ds = lbrace <>
             nest 4 (line <> stack ds) </>
             rbrace

pprAnti :: String -> String -> Doc
pprAnti anti s = char '$' <> text anti <> colon <>
                 if isIdentifier s then text s else nparens (text s)
  where
    isIdentifier :: String -> Bool
    isIdentifier []       = False
    isIdentifier ('_':cs) = all isIdChar cs
    isIdentifier (c:cs)   = isLower c && all isIdChar cs

    isIdChar :: Char -> Bool
    isIdChar '_' = True
    isIdChar c   = isAlphaNum c

class CFixity a where
    fixity :: a -> Fixity

    parensOp :: Int -> a -> Doc -> Doc
    parensOp prec op =
        nparensIf (prec > opPrec)
      where
        Fixity _ opPrec = fixity op

--
-- Fixities are taken from Table 2-1 in Section 2.12 of K&R (2nd ed.)
--
commaPrec :: Int
commaPrec = 1

commaPrec1 :: Int
commaPrec1 = commaPrec + 1

condPrec :: Int
condPrec = 3

condPrec1 :: Int
condPrec1 = condPrec + 1

unopPrec :: Int
unopPrec = 14

unopPrec1 :: Int
unopPrec1 = unopPrec + 1

memberPrec :: Int
memberPrec = 15

memberPrec1 :: Int
memberPrec1 = memberPrec + 1

instance CFixity BinOp where
    fixity Add  = infixl_ 12
    fixity Sub  = infixl_ 12
    fixity Mul  = infixl_ 13
    fixity Div  = infixl_ 13
    fixity Mod  = infixl_ 13
    fixity Eq   = infixl_ 9
    fixity Ne   = infixl_ 9
    fixity Lt   = infixl_ 10
    fixity Gt   = infixl_ 10
    fixity Le   = infixl_ 10
    fixity Ge   = infixl_ 10
    fixity Land = infixl_ 5
    fixity Lor  = infixl_ 4
    fixity And  = infixl_ 8
    fixity Or   = infixl_ 6
    fixity Xor  = infixl_ 7
    fixity Lsh  = infixl_ 11
    fixity Rsh  = infixl_ 11

    parensOp prec op =
        go op
      where
        go :: BinOp -> Doc -> Doc
        go Add  | isBitwiseOp = nparens
        go Sub  | isBitwiseOp = nparens
        go Land | isOp Lor    = nparens
        go Lor  | isOp Land   = nparens
        go And  | isOp Or     = nparens
                | isOp Xor    = nparens
        go Or   | isOp And    = nparens
                | isOp Xor    = nparens
        go Xor  | isOp And    = nparens
                | isOp Or     = nparens
        go _                  = nparensIf (prec > opPrec)

        isBitwiseOp :: Bool
        isBitwiseOp = isOp And || isOp Or || isOp Xor

        -- Return 'True' if we are potentially an immediate subterm of the
        -- binary operator op'. We make this determination based of the value of
        -- @prec@.
        isOp :: BinOp -> Bool
        isOp op' = prec == op'Prec || prec == op'Prec + 1
          where
            Fixity _ op'Prec = fixity op'

        Fixity _ opPrec = fixity op

instance CFixity AssignOp where
    fixity _ = infixr_ 2

instance CFixity UnOp where
    fixity _ = infixr_ unopPrec

instance Pretty Id where
    ppr (Id ident orig)  = addOrig orig $ text ident
    ppr (AntiId v orig)  = addOrig orig $ pprAnti "id" v

instance Pretty StringLit where
    ppr (StringLit ss _ orig) = addOrig orig $ sep (map string ss)

instance Pretty Storage where
    ppr (Tauto orig)                    = addOrig orig $ text "auto"
    ppr (Tregister orig)                = addOrig orig $ text "register"
    ppr (Tstatic orig)                  = addOrig orig $ text "static"
    ppr (Textern Nothing orig)          = addOrig orig $ text "extern"
    ppr (Textern (Just l) orig)         = addOrig orig $ text "extern" <+> ppr l
    ppr (Ttypedef orig)                 = addOrig orig $ text "typedef"

instance Pretty TypeQual where
    ppr (Tconst orig)          = addOrig orig $ text "const"
    ppr (Tvolatile orig)       = addOrig orig $ text "volatile"

    ppr (EscTypeQual esc orig) = addOrig orig $ text esc

    ppr (AntiTypeQual v orig)  = addOrig orig $ pprAnti "tyqual" v
    ppr (AntiTypeQuals v orig) = addOrig orig $ pprAnti "tyquals" v

    ppr (Tinline orig)         = addOrig orig $ text "inline"
    ppr (Trestrict orig)       = addOrig orig $ text "restrict"

    ppr (TAttr attr orig)      = addOrig orig $ ppr [attr]
    ppr (T__restrict orig)     = addOrig orig $ text "__restrict"

instance Pretty Sign where
    ppr (Tsigned orig)    = addOrig orig $ text "signed"
    ppr (Tunsigned orig)  = addOrig orig $ text "unsigned"

instance Pretty TypeSpec where
    ppr (Tvoid orig)            = addOrig orig $ text "void"
    ppr (Tchar sign orig)       = addOrig orig $ ppr sign <+> text "char"
    ppr (Tshort sign orig)      = addOrig orig $ ppr sign <+> text "short"
    ppr (Tint sign orig)        = addOrig orig $ ppr sign <+> text "int"
    ppr (Tlong sign orig)       = addOrig orig $ ppr sign <+> text "long"
    ppr (Tlong_long sign orig)  = addOrig orig $ ppr sign <+> text "long long"
    ppr (Tfloat orig)           = addOrig orig $ text "float"
    ppr (Tdouble orig)          = addOrig orig $ text "double"
    ppr (Tlong_double orig)     = addOrig orig $ text "long double"

    ppr (Tstruct maybe_ident maybe_fields attrs orig) =
        addOrig orig $
        align $ pprStructOrUnion "struct" maybe_ident maybe_fields attrs

    ppr (Tunion maybe_ident maybe_fields attrs orig) =
        addOrig orig $
        align $ pprStructOrUnion "union" maybe_ident maybe_fields attrs

    ppr (Tenum maybe_ident cenums attrs orig) =
        addOrig orig $
        align $ pprEnum maybe_ident cenums attrs

    ppr (Tnamed ident refs orig) =
        addOrig orig $
        ppr ident <> if null refs then empty else angles (ncommasep (map ppr refs))

    ppr (T_Bool orig) =
        addOrig orig $ text "_Bool"

    ppr (Tfloat_Complex orig) =
        addOrig orig $ text "float" <+> text "_Complex"

    ppr (Tdouble_Complex orig) =
        addOrig orig $ text "double" <+> text "_Complex"

    ppr (Tlong_double_Complex orig) =
        addOrig orig $ text "long" <+> text "double" <+> text "_Complex"

    ppr (Tfloat_Imaginary orig) =
        addOrig orig $ text "float" <+> text "_Imaginary"

    ppr (Tdouble_Imaginary orig) =
        addOrig orig $ text "double" <+> text "_Imaginary"

    ppr (Tlong_double_Imaginary orig) =
        addOrig orig $ text "long" <+> text "double" <+> text "_Imaginary"

    ppr (TtypeofExp e orig) =
        addOrig orig $ text "__typeof__" <> nparens (pprPrec 14 e)

    ppr (TtypeofType tipe orig) =
        addOrig orig $ text "__typeof__" <> nparens (ppr tipe)

    ppr (Tva_list orig) =
        addOrig orig $ text "__builtin_va_list"

pprStructOrUnion :: String
                 -> Maybe Id
                 -> Maybe [FieldGroup]
                 -> [Attr]
                 -> Doc
pprStructOrUnion ty maybe_ident maybe_fields attrs =
    text ty <+> ppr maybe_ident <+> ppr maybe_fields <+/> ppr attrs

pprEnum :: Maybe Id
        -> [CEnum]
        -> [Attr]
        -> Doc
pprEnum maybe_ident cenums attrs =
    text "enum" <+> ppr maybe_ident <+> ppr cenums <+/> ppr attrs

instance Pretty DeclSpec where
    ppr (DeclSpec storage quals spec orig) =
        addOrig orig $
        case map ppr storage ++ map ppr quals of
          []   -> ppr spec
          docs -> spread docs <+/> ppr spec

    ppr (AntiDeclSpec v orig) =
        addOrig orig $ pprAnti "spec" v

    ppr (AntiTypeDeclSpec storage quals v orig) =
        addOrig orig $
        spread (map ppr storage ++ map ppr quals) <+/>
        pprAnti "ty" v

instance Pretty ArraySize where
    ppr (ArraySize True e orig)  = addOrig orig $ text "static" <+> ppr e
    ppr (ArraySize False e orig) = addOrig orig $ ppr e
    ppr (VariableArraySize orig) = addOrig orig $ text "*"
    ppr (NoArraySize orig)       = addOrig orig $ empty

pprDeclarator :: Maybe Id -> Decl -> Doc
pprDeclarator maybe_ident declarator =
    case maybe_ident of
      Nothing ->    pprDecl declarator empty
      Just ident -> pprDecl declarator (ppr ident)
    where
      pprPtr :: Decl -> Doc -> (Decl, Doc)
      pprPtr (Ptr quals decl orig) post =
          pprPtr decl $
          (addOrig orig $ text "*" <> spread (map ppr quals)) <+> post

      pprPtr decl post =
          (decl, post)

      pprDirDecl :: Decl -> Doc -> (Decl, Doc)
      pprDirDecl (Array quals size decl orig) pre =
          pprDirDecl decl $
          pre <> (addOrig orig $ nbrackets (align (spread (map ppr quals) <+> ppr size)))

      pprDirDecl (Proto decl args orig) pre =
          pprDirDecl decl $
          pre <> (addOrig orig $ nparens (ppr args))

      pprDirDecl (OldProto decl args orig) pre =
          pprDirDecl decl $
          pre <> (addOrig orig $ parensList (map ppr args))

      pprDirDecl decl pre =
          (decl, pre)

      pprDecl :: Decl -> Doc -> Doc
      pprDecl decl mid =
          case decl' of
            DeclRoot orig       -> addOrig orig $ declDoc
            AntiTypeDecl _ orig -> addOrig orig $ declDoc
            _                   -> pprDecl decl' (nparens declDoc)
        where
          (decl', declDoc) = uncurry pprPtr (pprDirDecl decl mid)

instance Pretty Type where
    ppr (Type spec decl orig)  = addOrig orig $ ppr spec <+> pprDeclarator Nothing decl
    ppr (AntiType v orig)      = addOrig orig $ pprAnti "ty" v

instance Pretty Designator where
    ppr (IndexDesignator e orig)       = addOrig orig $ nbrackets $ ppr e
    ppr (MemberDesignator ident orig)  = addOrig orig $ dot <> ppr ident

instance Pretty Designation where
    ppr (Designation ds orig) = addOrig orig $ folddoc (<>) (map ppr ds)

instance Pretty Initializer where
    ppr (ExpInitializer e orig) = addOrig orig $ ppr e

    ppr (CompoundInitializer inits orig) =
        addOrig orig $
        bracesList (map pprInit inits)
      where
        pprInit :: (Maybe Designation, Initializer) -> Doc
        pprInit (Nothing, ini) = ppr ini
        pprInit (Just d, ini)  = ppr d <+> text "=" <//> ppr ini

    ppr (AntiInit v orig)  = addOrig orig $ pprAnti "init" v
    ppr (AntiInits v orig) = addOrig orig $ pprAnti "inits" v

instance Pretty Init where
    ppr (Init ident decl maybe_asmlabel maybe_e attrs orig) =
        addOrig orig $
        pprDeclarator (Just ident) decl <+/> ppr attrs
        <+> case maybe_asmlabel of
              Nothing -> empty
              Just l ->  text "asm" <+> nparens (ppr l)
        <+> case maybe_e of
              Nothing -> empty
              Just e ->  text "=" <+/> ppr e

instance Pretty Typedef where
    ppr (Typedef ident decl attrs orig) =
        addOrig orig $
        ppr (Init ident decl Nothing Nothing attrs orig)

instance Pretty InitGroup where
    ppr (InitGroup spec attrs inits orig) =
        addOrig orig $
        ppr spec <+/> ppr attrs <+> ncommasep (map ppr inits) <> semi -- added semi

    ppr (TypedefGroup spec attrs typedefs orig) =
        addOrig orig $
        text "typedef" <+> ppr spec <+/> ppr attrs <+> ncommasep (map ppr typedefs)

    ppr (AntiDecls v orig)  = addOrig orig $ pprAnti "decls" v
    ppr (AntiDecl v orig)   = addOrig orig $ pprAnti "decl" v

    pprList initgroups =
        stack (zipWith (<>) (map ppr initgroups) (repeat semi))

instance Pretty Field where
    ppr (Field maybe_ident maybe_decl maybe_e orig) =
        addOrig orig $
        case maybe_decl of
          Nothing   -> empty
          Just decl -> pprDeclarator maybe_ident decl
        <+>
        case maybe_e of
          Nothing -> empty
          Just e  -> colon <+> ppr e

instance Pretty FieldGroup where
    ppr (FieldGroup spec fields orig) =
        addOrig orig $
        ppr spec <+> ncommasep (map ppr fields)

    ppr (AntiSdecls v orig)  = addOrig orig $ pprAnti "sdecls" v
    ppr (AntiSdecl v orig)   = addOrig orig $ pprAnti "sdecl" v

    pprList fields = embrace (zipWith (<>) (map ppr fields) (repeat semi))

instance Pretty CEnum where
    ppr (CEnum ident maybe_e orig) =
        addOrig orig $
        ppr ident <+>
        case maybe_e of
          Nothing -> empty
          Just e ->  text "=" <+/> ppr e

    ppr (AntiEnums v orig)  = addOrig orig $ pprAnti "enums" v
    ppr (AntiEnum v orig)   = addOrig orig $ pprAnti "enum" v

    pprList []     = empty
    pprList cenums = embrace (zipWith (<>) (map ppr cenums) (repeat comma))

instance Pretty Attr where
    ppr (Attr ident [] orig) = addOrig orig $ ppr ident
    ppr (Attr ident args orig) =
        addOrig orig $
        ppr ident <> nparens (ncommasep (map ppr args))

    pprList []    = empty
    pprList attrs = text "__attribute__" <>
                    nparens (nparens (ncommasep (map ppr attrs)))

instance Pretty Param where
    ppr (Param maybe_ident spec decl orig) =
        addOrig orig $
        ppr spec <+> pprDeclarator maybe_ident decl

    ppr (AntiParams v orig)  = addOrig orig $ pprAnti "params" v
    ppr (AntiParam v orig)   = addOrig orig $ pprAnti "param" v

instance Pretty Params where
    ppr (Params args True orig) =
        addOrig orig $
        ncommasep (map ppr args ++ [text "..."])

    ppr (Params args False orig) =
        addOrig orig $
        ncommasep (map ppr args)

instance Pretty Func where
    ppr (Func spec ident decl args body orig) =
        addOrig orig $
        ppr spec <+> pprDeclarator (Just ident) (Proto decl args orig) </> ppr body

    ppr (OldFunc spec ident decl args maybe_initgroups body orig) =
        addOrig orig $
        ppr spec <+> pprDeclarator (Just ident) (OldProto decl args orig) </>
        ppr maybe_initgroups </>
        ppr body

instance Pretty Definition where
    ppr (FuncDef func orig)      = addOrig orig $ ppr func
    ppr (DecDef initgroup orig)  = addOrig orig $ ppr initgroup -- <> semi
    ppr (EscDef s orig)          = addOrig orig $ text s

    ppr (AntiFunc v orig)    = addOrig orig $ pprAnti "func" v
    ppr (AntiEsc v orig)     = addOrig orig $ pprAnti "esc" v
    ppr (AntiEdecls v orig)  = addOrig orig $ pprAnti "edecls" v
    ppr (AntiEdecl v orig)   = addOrig orig $ pprAnti "edecl" v

    pprList ds = stack (map ppr ds) <> line

instance Pretty Stm where
    ppr (Label ident attrs stm orig) =
        addOrig orig $
        nest (-2) (line <> ppr ident <> colon <+> ppr attrs) </> ppr stm

    ppr (Case e stm orig) =
        addOrig orig $
        nest (-2) (line <> text "case" <+> ppr e <> colon) </> ppr stm

    ppr (Default stm orig) =
        addOrig orig $
        nest (-2) (line <> text "default" <> colon) </> ppr stm

    ppr (Exp Nothing orig) = 
        addOrig orig $
        semi

    ppr (Exp (Just e) orig) =
        addOrig orig $
        nest 4 (ppr e) <> semi

    ppr (Block items orig) =
        addOrig orig $
        ppr items

    ppr (If test then' maybe_else orig) =
        addOrig orig $
        text "if" <+> nparens (ppr test) <>
        pprThen then' (fmap pprElse maybe_else)
      where
        pprThen :: Stm -> Maybe Doc -> Doc
        pprThen stm@(Block {}) rest        = space <> ppr stm <+> maybe empty id rest
        pprThen stm@(If {})    rest        = space <> ppr [BlockStm stm] <+> maybe empty id rest
        pprThen stm            Nothing     = nest 4 (line <> ppr stm)
        pprThen stm            (Just rest) = nest 4 (line <> ppr stm) </> rest

        pprElse :: Stm -> Doc
        pprElse stm =
            text "else" <> go stm
          where
            go :: Stm -> Doc
            go (Block {}) = space <> ppr stm
            go (If {})    = space <> ppr stm
            go _stm       = nest 4 (line <> ppr stm)

    ppr (Switch e stm orig) =
        addOrig orig $
        text "switch" <+> nparens (ppr e) <> pprBlock stm

    ppr (While e stm orig) =
        addOrig orig $
        text "while" <+> nparens (ppr e) <> pprBlock stm

    ppr (DoWhile stm e orig) =
        addOrig orig $
        text "do" <> pprBlock stm <+/> text "while" <> nparens (ppr e) <> semi

    ppr (For ini test post stm orig) =
        addOrig orig $
        text "for" <+>
        --(nparens . semisep) [either ppr ppr ini, ppr test, ppr post] <>
        nparens (either ppr (\me -> ppr me <> semi) ini <+> ppr test <> semi <+> ppr post) <>
        pprBlock stm

    ppr (Goto ident orig) =
        addOrig orig $
        text "goto" <+> ppr ident <> semi

    ppr (Continue orig) =
        addOrig orig $
        text "continue" <>semi

    ppr (Break orig) =
        addOrig orig $
        text "break" <> semi

    ppr (Return Nothing orig) =
        addOrig orig $
        text "return" <> semi

    ppr (Return (Just e) orig) =
        addOrig orig $
        nest 4 (text "return" <+> ppr e) <> semi

    ppr (Pragma pragma orig) =
        addOrig orig $
        text "#pragma" <+> text pragma

    ppr (Comment com stm orig) =
        addOrig orig $
        align $ text com </> ppr stm

    ppr (EscStm esc orig) =
        addOrig orig $
        text esc

    ppr (AntiEscStm v orig)      = addOrig orig $ pprAnti "escstm" v
    ppr (AntiPragma v orig)      = addOrig orig $ pprAnti "pragma" v
    ppr (AntiComment v stm orig) = addOrig orig $ pprAnti "pragma" v </> ppr stm
    ppr (AntiStm v orig)         = addOrig orig $ pprAnti "stm" v
    ppr (AntiStms v orig)        = addOrig orig $ pprAnti "stms" v

    ppr (Asm isVolatile _ template outs ins clobbered orig) =
        addOrig orig $
        text "__asm__"
        <> case isVolatile of
             True ->  space <> text "__volatile__"
             False -> empty
        <> nparens (ppr template
                   <> case outs of
                        [] -> space <> colon
                        _ ->  colon <+/> ppr outs
                   <> case ins of
                        [] -> space <> colon
                        _ ->  colon <+/> ppr ins
                   <> case clobbered of
                        [] -> space <> colon
                        _ ->  colon <+/> ncommasep (map text clobbered)
                  )
        <> semi

    ppr (AsmGoto isVolatile _ template ins clobbered labels orig) =
        addOrig orig $
        text "__asm__"
        <> case isVolatile of
             True ->  space <> text "__volatile__"
             False -> empty
        <> nparens (ppr template
                   <> colon
                   <> case ins of
                        [] -> space <> colon
                        _ ->  colon <+/> ppr ins
                   <> case clobbered of
                        [] -> space <> colon
                        _ ->  colon <+/> ncommasep (map text clobbered)
                   <> case clobbered of
                        [] -> space <> colon
                        _ ->  colon <+/> ncommasep (map ppr labels)
                  )
        <> semi

pprBlock :: Stm -> Doc
pprBlock stm@(Block {}) = space <> ppr stm
pprBlock stm@(If {})    = space <> ppr [BlockStm stm]
pprBlock stm            = nest 4 $ line <> ppr stm

instance Pretty BlockItem where
    ppr (BlockDecl decl) = ppr decl -- <> semi
    ppr (BlockStm stm)   = ppr stm

    ppr (AntiBlockItem v orig)  = addOrig orig $ pprAnti "item" v
    ppr (AntiBlockItems v orig) = addOrig orig $ pprAnti "items" v

    pprList = embrace . loop
      where
        loop :: [BlockItem] -> [Doc]
        loop [] =
            []
        loop [item] =
            [ppr item]
        loop (item1@(BlockDecl _) : item2@(BlockStm _) : items) =
            (ppr item1 <> line) : loop (item2 : items)
        loop (item1@(BlockStm _) : item2@(BlockDecl _) : items) =
            (ppr item1 <> line) : loop (item2 : items)
        loop (item : items) =
            ppr item : loop items

instance Pretty Const where
    pprPrec p (IntConst s _ i orig)       = addOrig orig $ nparensIf (i < 0 && p > unopPrec) $
                                            text s
    pprPrec p (LongIntConst s _ i orig)   = addOrig orig $ nparensIf (i < 0 && p > unopPrec) $
                                            text s
    pprPrec p (LongLongIntConst s _ i orig)  = addOrig orig $ nparensIf (i < 0 && p > unopPrec) $
                                               text s
    pprPrec p (FloatConst s r orig)       = addOrig orig $ nparensIf (r < 0 && p > unopPrec) $
                                            text s
    pprPrec p (DoubleConst s r orig)      = addOrig orig $ nparensIf (r < 0 && p > unopPrec) $
                                            text s
    pprPrec p (LongDoubleConst s r orig)  = addOrig orig $ nparensIf (r < 0 && p > unopPrec) $
                                            text s
    pprPrec _ (CharConst s _ orig)        = addOrig orig $ text s
    pprPrec _ (StringConst ss _ orig)     = addOrig orig $ sep (map string ss)

    pprPrec _ (AntiConst v orig)       = addOrig orig $ pprAnti "const"  v
    pprPrec _ (AntiString v orig)      = addOrig orig $ pprAnti "string"  v
    pprPrec _ (AntiChar v orig)        = addOrig orig $ pprAnti "char"    v
    pprPrec _ (AntiLongDouble v orig)  = addOrig orig $ pprAnti "ldouble" v
    pprPrec _ (AntiDouble v orig)      = addOrig orig $ pprAnti "double"  v
    pprPrec _ (AntiFloat v orig)       = addOrig orig $ pprAnti "float"   v
    pprPrec _ (AntiULInt v orig)       = addOrig orig $ pprAnti "ulint"   v
    pprPrec _ (AntiLInt v orig)        = addOrig orig $ pprAnti "lint"    v
    pprPrec _ (AntiULLInt v orig)      = addOrig orig $ pprAnti "ullint"  v
    pprPrec _ (AntiLLInt v orig)       = addOrig orig $ pprAnti "llint"   v
    pprPrec _ (AntiUInt v orig)        = addOrig orig $ pprAnti "uint"    v
    pprPrec _ (AntiInt v orig)         = addOrig orig $ pprAnti "int"     v

instance Pretty Exp where
    pprPrec p (Var ident orig) =
        addOrig orig $ 
        pprPrec p ident

    pprPrec p (Const k orig) =
        addOrig orig $ 
        pprPrec p k

    pprPrec p (BinOp op e1 e2 orig) =
        addOrig orig $ 
        infixop p op e1 e2

    pprPrec p (Assign e1 op e2 orig) =
        addOrig orig $ 
        infixop p op e1 e2

    pprPrec p (PreInc e orig) =
        addOrig orig $ 
        nparensIf (p > unopPrec) $
        text "++" <> pprPrec unopPrec1 e

    pprPrec p (PostInc e orig) =
        addOrig orig $ 
        nparensIf (p > unopPrec) $
        pprPrec unopPrec1 e <> text "++"

    pprPrec p (PreDec e orig) =
        addOrig orig $ 
        nparensIf (p > unopPrec) $
        text "--" <> pprPrec unopPrec1 e

    pprPrec p (PostDec e orig) =
        addOrig orig $ 
        nparensIf (p > unopPrec) $
        pprPrec unopPrec1 e <> text "--"

    pprPrec _ (EscExp e orig) =
        addOrig orig $ 
        text e

    pprPrec p (AntiEscExp e orig) =
        addOrig orig $ 
        nparensIf (p > unopPrec) $
        text e

    -- When printing leading + and - operators, we print the argument at
    -- precedence 'unopPrec1' to ensure we get parentheses in cases like
    -- @-(-42)@. The same holds for @++@ and @--@ above.
    pprPrec p (UnOp op@Positive e orig) =
        addOrig orig $ 
        nparensIf (p > unopPrec) $
        ppr op <> pprPrec unopPrec1 e

    pprPrec p (UnOp op@Negate e orig) =
        addOrig orig $ 
        nparensIf (p > unopPrec) $
        ppr op <> pprPrec unopPrec1 e

    pprPrec p (UnOp op e orig) =
        addOrig orig $ 
        prefixop p op e

    pprPrec p (SizeofExp e orig) =
        addOrig orig $ 
        nparensIf (p > unopPrec) $
        text "sizeof" <> nparens (ppr e)

    pprPrec p (SizeofType tipe orig) =
        addOrig orig $ 
        nparensIf (p > unopPrec) $
        text "sizeof" <> nparens (ppr tipe)

    pprPrec p (Cast tipe e orig) =
        addOrig orig $ 
        nparensIf (p > unopPrec) $
        nparens (ppr tipe) <+> pprPrec unopPrec e

    pprPrec p (Cond test then' else' orig) =
        addOrig orig $ 
        nparensIf (p > condPrec) $
        pprPrec condPrec1 test <+> text "?" <+>
        pprPrec condPrec1 then' <+> colon <+>
        pprPrec condPrec else'

    pprPrec p (Member e ident orig) =
        addOrig orig $ 
        nparensIf (p > memberPrec) $
        pprPrec memberPrec e <> dot <> ppr ident

    pprPrec p (PtrMember e ident orig) =
        addOrig orig $ 
        nparensIf (p > memberPrec) $
        pprPrec memberPrec e <> text "->" <> ppr ident

    pprPrec p (Index e1 e2 orig) =
        addOrig orig $ 
        nparensIf (p > memberPrec) $
        pprPrec memberPrec e1 <> nbrackets (ppr e2)

    pprPrec p (FnCall f args orig) =
        addOrig orig $ 
        nparensIf (p > memberPrec) $
        pprPrec memberPrec f <> parensList (map ppr args)

    pprPrec p (Seq e1 e2 orig) =
        addOrig orig $ 
        nparensIf (p > commaPrec) $
        pprPrec commaPrec e1 <> comma <+/> pprPrec commaPrec1 e2

    pprPrec p (CompoundLit ty inits orig) =
        addOrig orig $ 
        nparensIf (p > memberPrec) $
        nparens (ppr ty) <+>
        nbraces (ncommasep (map pprInit inits))
      where
        pprInit :: (Maybe Designation, Initializer) -> Doc
        pprInit (Nothing, ini) = ppr ini
        pprInit (Just d, ini)  = ppr d <+> text "=" <+/> ppr ini

    pprPrec _ (StmExpr blockItems orig) =
        addOrig orig $ 
        nparens $
        ppr blockItems

    pprPrec _ (BuiltinVaArg e ty orig) =
        addOrig orig $ 
        text "__builtin_va_arg(" <> ppr e <> comma <+> ppr ty <> rparen

    pprPrec _ (AntiArgs v orig)  = addOrig orig $ pprAnti "args"  v

    pprPrec _ (AntiExp v orig)   = addOrig orig $ pprAnti "var"  v

instance Pretty BinOp where
    ppr Add  = text "+"
    ppr Sub  = text "-"
    ppr Mul  = text "*"
    ppr Div  = text "/"
    ppr Mod  = text "%"
    ppr Eq   = text "=="
    ppr Ne   = text "!="
    ppr Lt   = text "<"
    ppr Gt   = text ">"
    ppr Le   = text "<="
    ppr Ge   = text ">="
    ppr Land = text "&&"
    ppr Lor  = text "||"
    ppr And  = text "&"
    ppr Or   = text "|"
    ppr Xor  = text "^"
    ppr Lsh  = text "<<"
    ppr Rsh  = text ">>"

instance Pretty AssignOp where
    ppr JustAssign = text "="
    ppr AddAssign  = text "+="
    ppr SubAssign  = text "-="
    ppr MulAssign  = text "*="
    ppr DivAssign  = text "/="
    ppr ModAssign  = text "%="
    ppr LshAssign  = text "<<="
    ppr RshAssign  = text ">>="
    ppr AndAssign  = text "&="
    ppr XorAssign  = text "^="
    ppr OrAssign   = text "|="

instance Pretty UnOp where
    ppr AddrOf   = text "&"
    ppr Deref    = text "*"
    ppr Positive = text "+"
    ppr Negate   = text "-"
    ppr Not      = text "~"
    ppr Lnot     = text "!"

instance Pretty AsmOut where
    ppr (AsmOut Nothing constraint ident) =
        text constraint <+> nparens (ppr ident)

    ppr (AsmOut (Just sym) constraint ident) =
        nbrackets (ppr sym) <+> text constraint <+> nparens (ppr ident)

    pprList []   = empty
    pprList outs = ncommasep (map ppr outs)

instance Pretty AsmIn where
    ppr (AsmIn Nothing constraint e) =
        text constraint <+> nparens (ppr e)

    ppr (AsmIn (Just sym) constraint e) =
        nbrackets (ppr sym) <+> text constraint <+> nparens (ppr e)

    pprList []  = empty
    pprList ins = ncommasep (map ppr ins)
