{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Util.Expr where

import Data.Maybe (catMaybes,fromJust)
import Data.List (nub,union,delete)
import Control.Monad (liftM)

import "language-c" Language.C as LC hiding (pretty,Pretty)
import Language.C.Analysis as LCA
import Language.C.Data.Ident as LCI
import qualified Language.C.Analysis.DefTable as LCD
import Language.C.Analysis.TravMonad (MonadTrav)

import Gencot.Util.Types (resolveTypedef,getCompType,getMemberDecl)

-- | Return the root identifier in the expression, if there is one.
getRootIdent :: LC.CExpr -> Maybe LCI.Ident
getRootIdent (LC.CVar nam _) = Just nam
getRootIdent (LC.CCast _ expr _) = getRootIdent expr
getRootIdent (LC.CUnary LC.CIndOp expr _) = getRootIdent expr
getRootIdent (LC.CIndex expr1 expr2 _) = getRootIdent expr1
getRootIdent (LC.CMember expr _ _ _) = getRootIdent expr
getRootIdent _ = Nothing

-- | Test whether an expression includes at least one derefence operation.
isReference :: LC.CExpr -> Bool
isReference (LC.CUnary LC.CIndOp _ _) = True
isReference (LC.CMember _ _ True n) = True
isReference (LC.CCast _ expr _) = isReference expr
isReference (LC.CIndex expr _ _) = isReference expr
isReference (LC.CMember expr _ _ _) = isReference expr
isReference _ = False

-- | Determine the type of an expression.
-- This is only implemented for an identifier with an optional
-- chain of member access operations.
-- Otherwise the result is Nothing.
getType :: MonadTrav m => LC.CExpr -> m (Maybe LCA.Type)
getType (LC.CMember expr mid isRef _) = do
    mtyp <- getType expr
    case mtyp of 
         Nothing -> return Nothing
         Just typ -> do
             dt <- LCA.getDefTable
             case getMemberDecl (getCompType typ dt) mid of
                  Nothing -> return Nothing
                  Just mdecl -> return $ Just $ LCA.declType mdecl
getType (LC.CVar sid _) = do
    msdecl <- LCA.lookupObject sid
    case msdecl of
         Nothing -> return Nothing
         Just decl -> return $ Just $ LCA.declType decl
getType _ = return Nothing 

-- | Check a for loop whether it can be translated.
-- The result is either a message why not, or the C expression for the upper limit of iterations.
checkForTrans :: LC.CStat -> Either String LC.CExpr
checkForTrans (LC.CFor _ Nothing _ _ _) = Left "No controlling expression"
checkForTrans (LC.CFor _ _ Nothing _ _) = Left "No step expression"
checkForTrans (LC.CFor c1 (Just e2) (Just e3) s _) =
    if null cntVars
    then Left "No counting variable found"
    else if null cntVars2
         then Left "Counting variables modified in body"
         else if null cntVars3
              then Left "Controlling expression modified"
              else if null cntVars4
                   then Left "No step found"
                   else if null exprsMax
                        then Left "No upper limit for iterations found"
                        else Right $ head exprsMax
    where cntVars = getForCntVars e2
          cntVars2 = filter (\(v,_,_) -> not $ modifiedInStat v s) cntVars
          cntVars3 = filter (\(_,_,e) -> not $ modif e) cntVars2
          modif e = any (\opd -> modifiedInStat opd s || modifiedInExpr opd e3) $ varOperands e
          cntVars4 = catMaybes $ map (getForStep e3) cntVars3
          exprsMax = catMaybes $ map getForMax $ map (getForInit c1) cntVars4

-- | The varOperands in an expression are the subexpressions for variables and struct member access sequences starting with a variable
varOperands :: LC.CExpr -> [LC.CExpr]
varOperands e@(LC.CVar _ _) = [e]
varOperands (LC.CComma es _) = concat $ map varOperands es
varOperands (LC.CAssign _ e1 e2 _) = (varOperands e1) ++ (varOperands e2)
varOperands (LC.CCond e (Just e1) e2 _) = (varOperands e) ++ (varOperands e1) ++ (varOperands e2)
varOperands (LC.CCond e Nothing e2 _) = (varOperands e) ++ (varOperands e2)
varOperands (LC.CBinary _ e1 e2 _) = (varOperands e1) ++ (varOperands e2)
varOperands (LC.CCast _ e _) = varOperands e
varOperands (LC.CUnary _ e _) = varOperands e
varOperands (LC.CComplexReal e _) = varOperands e
varOperands (LC.CComplexImag e _) = varOperands e
varOperands (LC.CIndex e1 e2 _) = (varOperands e1) ++ (varOperands e2)
varOperands (LC.CCall e es _) = (varOperands e) ++ (concat $ map varOperands es)
varOperands e@(LC.CMember e1 _ _ _) | memvar e1 = [e]
    where memvar (LC.CVar _ _) = True
          memvar (LC.CMember e _ _ _) = memvar e
          memvar _ = False
varOperands _ = []

-- | Is a varOperand e modified in an expression?
modifiedInExpr :: LC.CExpr -> LC.CExpr -> Bool
modifiedInExpr e (LC.CAssign _ e1 e2 _) = matchPartOfLvalue e e1 || modifiedInExpr e e2
modifiedInExpr e (LC.CUnary op e1 _) | elem op [LC.CPreIncOp,LC.CPreDecOp,LC.CPostIncOp,LC.CPostDecOp] = matchPartOfLvalue e e1
modifiedInExpr e (LC.CUnary op e1 _) = modifiedInExpr e e1
modifiedInExpr e (LC.CComma es _) = any (modifiedInExpr e) es
modifiedInExpr e (LC.CCond e1 (Just e2) e3 _) = (modifiedInExpr e e1) || (modifiedInExpr e e2) || (modifiedInExpr e e3)
modifiedInExpr e (LC.CCond e1 Nothing e3 _) = (modifiedInExpr e e1) || (modifiedInExpr e e3)
modifiedInExpr e (LC.CBinary _ e1 e2 _) = (modifiedInExpr e e1) || (modifiedInExpr e e2)
modifiedInExpr e (LC.CCast _ e1 _) = modifiedInExpr e e1
modifiedInExpr e (LC.CComplexReal e1 _) = modifiedInExpr e e1
modifiedInExpr e (LC.CComplexImag e1 _) = modifiedInExpr e e1
modifiedInExpr e (LC.CIndex e1 e2 _) = (modifiedInExpr e e1) || (modifiedInExpr e e2)
modifiedInExpr e (LC.CCall e1 es _) = (modifiedInExpr e e1) || (any (modifiedInExpr e) es)
modifiedInExpr e (LC.CMember e1 _ _ _) = modifiedInExpr e e1
modifiedInExpr _ _ = False

-- | Is a varOperand e a syntactic part of an lvalue, so that it is modified by modifying the lvalue
matchPartOfLvalue :: LC.CExpr -> LC.CExpr -> Bool
matchPartOfLvalue e@(LC.CMember e1 m1 _ _) (LC.CMember e2 m2 _ _) | m1 == m2 = matchPartOfLvalue e1 e2 || matchPartOfLvalue e e2
matchPartOfLvalue (LC.CVar nam1 _) (LC.CVar nam2 _) = nam1 == nam2
matchPartOfLvalue e (LC.CIndex e1 e2 _) = matchPartOfLvalue e e1
matchPartOfLvalue _ _ = False

-- | Is a varOperand e modified in a statement?
modifiedInStat :: LC.CExpr -> LC.CStat -> Bool
modifiedInStat e (LC.CLabel _ s _ _) = modifiedInStat e s
modifiedInStat e (LC.CCase _ s _) = modifiedInStat e s
modifiedInStat e (LC.CCases _ _ s _) = modifiedInStat e s
modifiedInStat e (LC.CDefault s _) = modifiedInStat e s
modifiedInStat e (LC.CExpr (Just e1) _) = modifiedInExpr e e1
modifiedInStat e (LC.CCompound _ bis _) = any modifiedInBlockItem bis
    where modifiedInBlockItem (LC.CBlockStmt s) = modifiedInStat e s
          modifiedInBlockItem (LC.CBlockDecl d) = modifiedInDecl e d
modifiedInStat e (LC.CIf e1 s1 (Just s2) _) = modifiedInExpr e e1 || modifiedInStat e s1 || modifiedInStat e s2
modifiedInStat e (LC.CIf e1 s1 Nothing _) = modifiedInExpr e e1 || modifiedInStat e s1
modifiedInStat e (LC.CSwitch e1 s _) = modifiedInExpr e e1 || modifiedInStat e s
modifiedInStat e (LC.CWhile e1 s _ _) = modifiedInExpr e e1 || modifiedInStat e s
modifiedInStat e (LC.CFor (Left me1) me2 me3 s _) = 
    maybe False (modifiedInExpr e) me1 || maybe False (modifiedInExpr e) me2 ||
    maybe False (modifiedInExpr e) me3 || modifiedInStat e s
modifiedInStat e (LC.CFor (Right d) me2 me3 s _) = 
    modifiedInDecl e d || maybe False (modifiedInExpr e) me2 ||
    maybe False (modifiedInExpr e) me3 || modifiedInStat e s
modifiedInStat e (LC.CGotoPtr e1 _) = modifiedInExpr e e1
modifiedInStat e (LC.CReturn me1 _) = maybe False (modifiedInExpr e) me1
modifiedInStat _ _ = False

modifiedInDecl e (LC.CStaticAssert _ _ _) = False
modifiedInDecl e (LC.CDecl _ dcs _) = any modifiedInDeclr dcs
    where modifiedInDeclr (_,Nothing,_) = False
          modifiedInDeclr (_,Just i,_) = modifiedInInit i
          modifiedInInit (LC.CInitExpr e1 _) = modifiedInExpr e e1
          modifiedInInit (LC.CInitList il _) = any modifiedInIList il
          modifiedInIList (desigs, i) = modifiedInInit i || any modifiedInDesig desigs
          modifiedInDesig (LC.CArrDesig e1 _) = modifiedInExpr e e1
          modifiedInDesig (LC.CMemberDesig _ _) = False
          modifiedInDesig (LC.CRangeDesig e1 e2 _) = modifiedInExpr e e1 || modifiedInExpr e e2

-- | Return a list of counting variable candidates with their relation operators and control expression.
-- v is a candidate if the expression is (a conjunction containing) the relation v rel evl, 
-- where rel is one of <, <=, >, >=, != and v does not occur free in evl.
getForCntVars :: LC.CExpr -> [(LC.CExpr,LC.CBinaryOp,LC.CExpr)]
getForCntVars (LC.CBinary op v@(LC.CVar nam _) e _) 
    | elem op [LC.CLeOp,LC.CGrOp,LC.CLeqOp,LC.CGeqOp,LC.CNeqOp] && (not (elem nam $ getFreeInCExpr e)) = [(v,op,e)]
getForCntVars (LC.CBinary LC.CLndOp e1 e2 _) = (getForCntVars e1) ++ (getForCntVars e2) 
getForCntVars _ = []

-- | Add the step value (positive or negative), if found.
-- A step value is found if the expression e contains exactly one assignment to v which increments or decrements
-- v by a constant value.
getForStep :: LC.CExpr -> (LC.CExpr,LC.CBinaryOp,LC.CExpr) -> Maybe (LC.CExpr,LC.CBinaryOp,LC.CExpr,Integer)
getForStep e (v,o,ce) = 
    if length ass /= 1
       then Nothing
       else case getStep $ head ass of
                 Nothing -> Nothing
                 Just stp -> Just (v,o,ce,stp)
    where ass = getAssignments v e
          getStep (LC.CUnary op _ _) | elem op [LC.CPreIncOp,LC.CPostIncOp] = Just 1
          getStep (LC.CUnary op _ _) | elem op [LC.CPreDecOp,LC.CPostDecOp] = Just (-1)
          getStep (LC.CAssign LC.CAddAssOp _ (LC.CConst (LC.CIntConst i _)) _) = Just $ LC.getCInteger i
          getStep (LC.CAssign LC.CSubAssOp _ (LC.CConst (LC.CIntConst i _)) _) = Just (- (LC.getCInteger i))
          getStep (LC.CAssign LC.CAssignOp (LC.CVar nam _) (LC.CBinary LC.CAddOp (LC.CVar nam' _) (LC.CConst (LC.CIntConst i _)) _) _)
            | nam == nam' = Just $ LC.getCInteger i
          getStep (LC.CAssign LC.CAssignOp (LC.CVar nam _) (LC.CBinary LC.CSubOp (LC.CVar nam' _) (LC.CConst (LC.CIntConst i _)) _) _)
            | nam == nam' = Just $ (- (LC.getCInteger i))
          getStep (LC.CAssign LC.CAssignOp (LC.CVar nam _) (LC.CBinary LC.CAddOp (LC.CConst (LC.CIntConst i _)) (LC.CVar nam' _) _) _)
            | nam == nam' = Just $ LC.getCInteger i
          getStep _ = Nothing

-- | Return all assignments to a given variable in an expression
getAssignments :: LC.CExpr -> LC.CExpr -> [LC.CExpr]
getAssignments (LC.CVar nam _) e@(LC.CUnary op (LC.CVar nam' _) _)
    | elem op [LC.CPreIncOp,LC.CPreDecOp,LC.CPostIncOp,LC.CPostDecOp] && nam' == nam = [e]
getAssignments (LC.CVar nam _) e@(LC.CAssign op (LC.CVar nam' _) _ _) | nam' == nam = [e]
getAssignments v (LC.CComma es _) = concat $ map (getAssignments v) es
getAssignments _ _ = []

-- | Add expression for initial value, if found.
-- An initial value ini is found if the clause is an expression containing exactly one assignment to v of the form v = ini 
-- or a declaration containing a declarator of the form v = ini.
getForInit :: (Either (Maybe LC.CExpr) LC.CDecl) -> (LC.CExpr,LC.CBinaryOp,LC.CExpr,Integer) -> (LC.CExpr,LC.CBinaryOp,LC.CExpr,Integer,Maybe LC.CExpr)
getForInit (Left Nothing) (v,o,e,s) = (v,o,e,s,Nothing)
getForInit (Left (Just e1)) (v@(LC.CVar vnam _),o,e,s) = (v,o,e,s,if length ass == 1 then getInit e1 else Nothing)
    where ass = getAssignments v e1
          getInit (LC.CAssign LC.CAssignOp (LC.CVar vnam _) i _) = Just i
          getInit (LC.CComma es _) = 
              let is = catMaybes $ map getInit es
              in if null is then Nothing else Just $ head is
          getInit _ = Nothing
getForInit (Right (LC.CDecl specs dcs _)) (v@(LC.CVar vnam _),o,e,s) =
    if length is == 1
       then (v,o,e,s,Just $ head is)
       else (v,o,e,s,Nothing)
    where is = catMaybes $ map getInit dcs
          -- If a counter variable is declared but not initialized it is useless for counting down
          getInit (Just (LC.CDeclr (Just vnam) _ _ _ _),(Just (LC.CInitExpr e _)),_) = Just e
          getInit _ = Nothing

getForMax :: (LC.CExpr,LC.CBinaryOp,LC.CExpr,Integer,Maybe LC.CExpr) -> Maybe LC.CExpr
getForMax (_,op,e,stp,_) | elem op [LC.CLeOp,LC.CLeqOp] =
    if stp > 0 then Just e else Nothing
getForMax (_,op,_,stp,mi) | elem op [LC.CGrOp,LC.CGeqOp] =
    if stp < 0 then mi else Nothing
getForMax (_,LC.CNeqOp,_,_,Nothing) = Nothing
getForMax (_,LC.CNeqOp,ee@(LC.CConst (LC.CIntConst ie _)),stp,Just ei@(LC.CConst (LC.CIntConst ii _))) =
    if lo < hi then Just ehi else Nothing
    where ie' = LC.getCInteger ie
          ii' = LC.getCInteger ii
          hi = if stp == 1 then ie' else ii'
          lo = if stp == 1 then ii' else ie'
          ehi = if stp == 1 then ee else ei
getForMax _ = Nothing

-- | All identifiers which occur free in an expression, including the names of invoked functions.
-- These are all identifiers in the expression, since identifiers cannot be bound in an expression.
-- Identifiers are returned in arbitrary order, every identifier appears only once.
getFreeInCExpr :: LC.CExpr -> [LCI.Ident]
getFreeInCExpr (LC.CVar nam _) = [nam]
getFreeInCExpr (LC.CComma es _) = nub $ concat $ map getFreeInCExpr es
getFreeInCExpr (LC.CAssign _ e1 e2 _) = union (getFreeInCExpr e1) (getFreeInCExpr e2)
getFreeInCExpr (LC.CCond e (Just e1) e2 _) = union (getFreeInCExpr e) $ union (getFreeInCExpr e1) (getFreeInCExpr e2)
getFreeInCExpr (LC.CCond e Nothing e2 _) = union (getFreeInCExpr e) (getFreeInCExpr e2)
getFreeInCExpr (LC.CBinary _ e1 e2 _) = union (getFreeInCExpr e1) (getFreeInCExpr e2)
getFreeInCExpr (LC.CCast _ e _) = getFreeInCExpr e
getFreeInCExpr (LC.CUnary _ e _) = getFreeInCExpr e
getFreeInCExpr (LC.CComplexReal e _) = getFreeInCExpr e
getFreeInCExpr (LC.CComplexImag e _) = getFreeInCExpr e
getFreeInCExpr (LC.CIndex e1 e2 _) = union (getFreeInCExpr e1) (getFreeInCExpr e2)
getFreeInCExpr (LC.CCall e es _) = union (getFreeInCExpr e) $ nub $ concat $ map getFreeInCExpr es
getFreeInCExpr (LC.CMember e _ _ _) = getFreeInCExpr e
getFreeInCExpr _ = []

-- | All identifiers which occur free in a statement.
-- Identifiers are returned in arbitrary order, every identifier appears only once.
getFreeInCStat :: LC.CStat -> [LCI.Ident]
getFreeInCStat (LC.CLabel _ s _ _) = getFreeInCStat s
getFreeInCStat (LC.CCase _ s _) = getFreeInCStat s
getFreeInCStat (LC.CCases _ _ s _) = getFreeInCStat s
getFreeInCStat (LC.CDefault s _) = getFreeInCStat s
getFreeInCStat (LC.CExpr (Just e1) _) = getFreeInCExpr e1
getFreeInCStat (LC.CCompound _ bis _) = getFreeInBlockItems bis
    where getFreeInBlockItems [] = []
          getFreeInBlockItems ((LC.CBlockStmt s) : bis) = union (getFreeInCStat s) $ getFreeInBlockItems bis
          getFreeInBlockItems ((LC.CBlockDecl d) : bis) = getFreeInDeclBlock d $ getFreeInBlockItems bis
getFreeInCStat (LC.CIf e1 s1 (Just s2) _) = union (getFreeInCExpr e1) $ union (getFreeInCStat s1) (getFreeInCStat s2)
getFreeInCStat (LC.CIf e1 s1 Nothing _) = union (getFreeInCExpr e1) (getFreeInCStat s1)
getFreeInCStat (LC.CSwitch e1 s _) = union (getFreeInCExpr e1) (getFreeInCStat s)
getFreeInCStat (LC.CWhile e1 s _ _) = union (getFreeInCExpr e1) (getFreeInCStat s)
getFreeInCStat (LC.CFor (Left me1) me2 me3 s _) = 
    union (maybe [] getFreeInCExpr me1) $ union (maybe [] getFreeInCExpr me2)
    $ union (maybe [] getFreeInCExpr me3) (getFreeInCStat s)
getFreeInCStat (LC.CFor (Right d) me2 me3 s _) = 
    getFreeInDeclBlock d $ union (maybe [] getFreeInCExpr me2)
    $ union (maybe [] getFreeInCExpr me3) (getFreeInCStat s)
getFreeInCStat (LC.CGotoPtr e1 _) = getFreeInCExpr e1
getFreeInCStat (LC.CReturn me1 _) = maybe [] getFreeInCExpr me1
getFreeInCStat _ = []

getFreeInDeclBlock (LC.CStaticAssert _ _ _) vs = vs
getFreeInDeclBlock (LC.CDecl _ dcs _) vs = getFreeInDeclrsBlock dcs vs 
getFreeInDeclrsBlock [] vs = vs
getFreeInDeclrsBlock (dc : dcs) vs = getFreeInDeclrBlock dc $ getFreeInDeclrsBlock dcs vs
getFreeInDeclrBlock (Just (LC.CDeclr (Just nam) _ _ _ _),mi,_) vs = 
    union (maybe [] getFreeInCInit mi) $ delete nam vs 
getFreeInCInit (LC.CInitExpr e _) = getFreeInCExpr e
getFreeInCInit (LC.CInitList il _) = nub $ concat $ map getFreeInCInitListEl il
getFreeInCInitListEl (desigs, i) = union (getFreeInCInit i) $ nub $ concat $ map getFreeInDesig desigs
getFreeInDesig (LC.CArrDesig e _) = getFreeInCExpr e
getFreeInDesig (LC.CMemberDesig _ _) = []
getFreeInDesig (LC.CRangeDesig e1 e2 _) = union (getFreeInCExpr e1) (getFreeInCExpr e2)
