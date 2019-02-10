{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}

{- This is a modified version of Language.C.Syntax 
   from package language-c-quote 
   by Geoffrey Mainland and Manuel M T Chakravarty
   Modifications are:
   - removed Clang blocks and Objective-C parts 
   - removed utility functions at end
   - replaced SrcLoc component in every AST node by Origin.
-}
module Gencot.C.Ast where

import Data.Data (Data(..))
--import Data.Loc
import Data.String (IsString(..))
import Data.Typeable (Typeable)

import Gencot.Origin

data Id = Id     String Origin
        | AntiId String Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data StringLit = StringLit [String] String Origin
    deriving (Eq, Ord, Show, Data, Typeable)

type Linkage = StringLit

data Storage = Tauto                   Origin
             | Tregister               Origin
             | Tstatic                 Origin
             | Textern (Maybe Linkage) Origin
             | Ttypedef                Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data TypeQual = Tconst    Origin
              | Tvolatile Origin

              | EscTypeQual String Origin

              | AntiTypeQual  String Origin
              | AntiTypeQuals String Origin

              -- C99
              | Tinline   Origin
              | Trestrict Origin

              -- GCC
              | T__restrict Origin
              | TAttr Attr

    deriving (Eq, Ord, Show, Data, Typeable)

data Sign = Tsigned   Origin
          | Tunsigned Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data TypeSpec = Tvoid                   Origin
              | Tchar      (Maybe Sign) Origin
              | Tshort     (Maybe Sign) Origin
              | Tint       (Maybe Sign) Origin
              | Tlong      (Maybe Sign) Origin
              | Tlong_long (Maybe Sign) Origin
              | Tfloat                  Origin
              | Tdouble                 Origin
              | Tlong_double            Origin
              | Tstruct (Maybe Id) (Maybe [FieldGroup]) [Attr] Origin
              | Tunion  (Maybe Id) (Maybe [FieldGroup]) [Attr] Origin
              | Tenum   (Maybe Id) [CEnum]              [Attr] Origin
              | Tnamed Id       -- A typedef name
                       [Id]     -- Objective-C protocol references
                       Origin

              -- C99
              | T_Bool                 Origin
              | Tfloat_Complex         Origin
              | Tdouble_Complex        Origin
              | Tlong_double_Complex   Origin
              | Tfloat_Imaginary       Origin
              | Tdouble_Imaginary      Origin
              | Tlong_double_Imaginary Origin

              -- Gcc
              | TtypeofExp  Exp  Origin
              | TtypeofType Type Origin
              | Tva_list         Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data DeclSpec = DeclSpec         [Storage] [TypeQual] TypeSpec Origin
              | AntiDeclSpec                          String   Origin
              | AntiTypeDeclSpec [Storage] [TypeQual] String   Origin
    deriving (Eq, Ord, Show, Data, Typeable)

-- | There are two types of declarators in C, regular declarators and abstract
-- declarators. The former is for declaring variables, function parameters,
-- typedefs, etc. and the latter for abstract types---@typedef int
-- ({*}foo)(void)@ vs. @\tt int ({*})(void)@. The difference between the two is
-- just whether or not an identifier is attached to the declarator. We therefore
-- only define one 'Decl' type and use it for both cases.

data ArraySize = ArraySize Bool Exp Origin
               | VariableArraySize Origin
               | NoArraySize Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data Decl = DeclRoot Origin
          | Ptr [TypeQual] Decl Origin
          | Array [TypeQual] ArraySize Decl Origin
          | Proto Decl Params Origin
          | OldProto Decl [Id] Origin
          | AntiTypeDecl String Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data Type = Type DeclSpec Decl Origin
          | AntiType String Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data Designator = IndexDesignator Exp Origin
                | MemberDesignator Id Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data Designation = Designation [Designator] Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data Initializer = ExpInitializer Exp Origin
                 | CompoundInitializer [(Maybe Designation, Initializer)] Origin
                 | AntiInit  String Origin
                 | AntiInits String Origin
    deriving (Eq, Ord, Show, Data, Typeable)

type AsmLabel = StringLit

data Init = Init Id Decl (Maybe AsmLabel) (Maybe Initializer) [Attr] Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data Typedef = Typedef Id Decl [Attr] Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data InitGroup = InitGroup    DeclSpec [Attr] [Init]    Origin
               | TypedefGroup DeclSpec [Attr] [Typedef] Origin
               | AntiDecl  String Origin
               | AntiDecls String Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data Field = Field (Maybe Id) (Maybe Decl) (Maybe Exp) Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data FieldGroup  =  FieldGroup DeclSpec [Field] Origin
                 |  AntiSdecl  String Origin
                 |  AntiSdecls String Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data CEnum  =  CEnum Id (Maybe Exp) Origin
            |  AntiEnum  String Origin
            |  AntiEnums String Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data Attr  =  Attr Id [Exp] Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data Param  =  Param (Maybe Id) DeclSpec Decl Origin
            |  AntiParam  String Origin
            |  AntiParams String Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data Params = Params [Param] Bool Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data Func  =  Func    DeclSpec Id Decl Params                   [BlockItem] Origin
           |  OldFunc DeclSpec Id Decl [Id] (Maybe [InitGroup]) [BlockItem] Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data Definition  =  FuncDef    Func      Origin
                 |  DecDef     InitGroup Origin
                 |  EscDef     String    Origin
                 |  AntiFunc   String    Origin
                 |  AntiEsc    String    Origin
                 |  AntiEdecl  String    Origin
                 |  AntiEdecls String    Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data Stm  = Label Id [Attr] Stm Origin
          | Case Exp Stm Origin
          | Default Stm Origin
          | Exp (Maybe Exp) Origin
          | Block [BlockItem] Origin
          | If Exp Stm (Maybe Stm) Origin
          | Switch Exp Stm Origin
          | While Exp Stm Origin
          | DoWhile Stm Exp Origin
          | For (Either InitGroup (Maybe Exp)) (Maybe Exp) (Maybe Exp) Stm Origin
          | Goto Id Origin
          | Continue Origin
          | Break Origin
          | Return (Maybe Exp) Origin
          | Pragma String Origin
          | Comment String Stm Origin
          | EscStm String Origin
          | AntiEscStm String Origin
          | AntiPragma String Origin
          | AntiComment String Stm Origin
          | AntiStm String Origin
          | AntiStms String Origin

          -- GCC
          | Asm Bool         -- @True@ if volatile, @False@ otherwise
                [Attr]       -- Attributes
                AsmTemplate  -- Assembly template
                [AsmOut]     -- Output operands
                [AsmIn]      -- Input operands
                [AsmClobber] -- Clobbered registers
                Origin
          | AsmGoto Bool         -- @True@ if volatile, @False@ otherwise
                    [Attr]       -- Attributes
                    AsmTemplate  -- Assembly template
                    [AsmIn]      -- Input operands
                    [AsmClobber] -- Clobbered registers
                    [Id]         -- Labels
                    Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data BlockItem = BlockDecl InitGroup
               | BlockStm Stm
               | AntiBlockItem  String Origin
               | AntiBlockItems String Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data Signed = Signed
            | Unsigned
    deriving (Eq, Ord, Show, Data, Typeable)

-- | The 'String' parameter to 'Const' data constructors is the raw string
-- representation of the constant as it was parsed.
data Const = IntConst         String   Signed Integer Origin
           | LongIntConst     String   Signed Integer Origin
           | LongLongIntConst String   Signed Integer Origin
           | FloatConst       String   Float          Origin
           | DoubleConst      String   Double         Origin
           | LongDoubleConst  String   Double         Origin
           | CharConst        String   Char           Origin
           | StringConst      [String] String         Origin

           | AntiConst      String Origin
           | AntiInt        String Origin
           | AntiUInt       String Origin
           | AntiLInt       String Origin
           | AntiULInt      String Origin
           | AntiLLInt      String Origin
           | AntiULLInt     String Origin
           | AntiFloat      String Origin
           | AntiDouble     String Origin
           | AntiLongDouble String Origin
           | AntiChar       String Origin
           | AntiString     String Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data Exp = Var Id Origin
         | Const Const Origin
         | BinOp BinOp Exp Exp Origin
         | Assign Exp AssignOp Exp Origin
         | PreInc Exp Origin
         | PostInc Exp Origin
         | PreDec Exp Origin
         | PostDec Exp Origin
         | UnOp UnOp Exp Origin
         | SizeofExp Exp Origin
         | SizeofType Type Origin
         | Cast Type Exp Origin
         | Cond Exp Exp Exp Origin
         | Member Exp Id Origin
         | PtrMember Exp Id Origin
         | Index Exp Exp Origin
         | FnCall Exp [Exp] Origin
         | Seq Exp Exp Origin
         | CompoundLit Type [(Maybe Designation, Initializer)] Origin
         | StmExpr [BlockItem] Origin
         | EscExp String Origin
         | AntiEscExp String Origin
         | AntiExp String Origin
         | AntiArgs String Origin

         -- GCC
         | BuiltinVaArg Exp Type Origin
    deriving (Eq, Ord, Show, Data, Typeable)

data BinOp = Add
           | Sub
           | Mul
           | Div
           | Mod
           | Eq
           | Ne
           | Lt
           | Gt
           | Le
           | Ge
           | Land
           | Lor
           | And
           | Or
           | Xor
           | Lsh
           | Rsh
    deriving (Eq, Ord, Show, Data, Typeable)

data AssignOp = JustAssign
              | AddAssign
              | SubAssign
              | MulAssign
              | DivAssign
              | ModAssign
              | LshAssign
              | RshAssign
              | AndAssign
              | XorAssign
              | OrAssign
    deriving (Eq, Ord, Show, Data, Typeable)

data UnOp = AddrOf
          | Deref
          | Positive
          | Negate
          | Not
          | Lnot
    deriving (Eq, Ord, Show, Data, Typeable)

{------------------------------------------------------------------------------
 -
 - GCC extensions
 -
 ------------------------------------------------------------------------------}

type AsmTemplate = StringLit

data AsmOut = AsmOut (Maybe Id) String Id
    deriving (Eq, Ord, Show, Data, Typeable)

data AsmIn = AsmIn (Maybe Id) String Exp
    deriving (Eq, Ord, Show, Data, Typeable)

type AsmClobber = String

{------------------------------------------------------------------------------
 -
 - Instances
 -
 ------------------------------------------------------------------------------}

instance IsString Id where
    fromString s = Id s noOrigin

instance IsString StringLit where
    fromString s = StringLit [s] s noOrigin
