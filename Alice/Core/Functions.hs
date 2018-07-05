module Alice.Core.Functions where

import Alice.Data.Base
import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Text
import Alice.Prove.Normalize
import Alice.Core.Base

import qualified Control.Monad.Writer as W
import Data.List
import Control.Monad
import Data.Maybe
import Debug.Trace
import Control.Monad.State


{- generate proof task associated with a block -}

prfTask Select vs fr = foldr mbExi fr vs
prfTask Declare _ fr
    | funDcl fr = funTask fr
    | setDcl fr = setTask fr
prfTask _ _ fr = fr

funDcl (And f _) = trId f == funId
setDcl (And f _) = trId f == setId

setTask (And _ (All _ (Iff _ (Tag DRP f)))) = rep f -- replacement schema
setTask (And _ (All _ (Iff _ f))) = sep f -- separation schema
funTask h@(And k (And g f)) = let c = dmcnd g in domain g `blAnd` c (choices f `blAnd` existence f `blAnd` uniqueness f) `blAnd` ((k `And` g) `blImp` well_founded f) `blAnd` property h

domain (Tag DDM (All _ (Iff _ f))) = Tag FDM $ sep f



choices = Tag FCH . dive
  where
    dive (Tag DPR _) = Top -- ignore property formula
    dive (Tag DEV _) = Top
    dive (Tag _ f) = dive f
    dive (Exi x (And (Tag DEF f) g)) = (prfTask Declare [] $ dec $ inst x $ f) `blAnd` (dec $ inst x $ f `blImp` dive g)
    dive (All x f) =  blAll x $ dive f
    dive (Imp f g) = f `blImp` dive g
    dive (Exi x f) = blExi x $ dive f
    dive (And f g) = dive f `blAnd` dive g
    dive f = f

existence f = let ((trm, nm, rst), cond) = conditions f
               in Tag FEX $ allDom nm $ foldr mbExi (foldr blAnd Top cond `blAnd` equ trm `blAnd` cases rst `blAnd` (dive rst)) (onlyFree 'c' [] trm)
  where
    dive (And f g) = dive f `blImp` dive g
    dive (Imp f g) = f `blImp` dive g
    dive (Exi x f) = blAll x $ dive f
    dive (Tag DEV f) = form f
    dive f = f

    form Trm{trName = "="} = Top
    form (All x (Iff f g)) = Exi x g

    equ trm = zEqu trm (zVar "")
    allDom nm = zAll "" . blImp (zElem (zVar "") (zDom nm))

    cases (And f g) = cases f `Or` cases g
    cases (Imp f g) = f
    cases _ = Top

conditions = W.runWriter . dive
  where
    dive (And f g) = dive g -- ignore possible property formula
    dive (All x f) = dive $ inst ('c':x) f
    dive (Imp f g) = W.tell [f] >> dive g
    dive (Tag DCD (Imp Trm{trArgs = [t,Trm{trArgs = [f]}]} rst)) = return (t, f, rst)




sep (And f g) = sep f
sep t = dec $ zSet $ last $ trArgs t -- we know that in this case t is the term zElem(. , .), where the second argument is the term whose sethood we have to show

rep = dive []
  where
    dive vs (Exi x f) = dive (x:vs) f
    dive vs (And f g) = let vs2 = map ((:) 'c') vs
                         in foldr mbExi (sets vs2 `blAnd` foldr mbAll (f `blImp` elms vs vs2) vs) vs2
    sets = foldr blAnd Top . map (zSet . zVar)
    elms (v1:vs) (v2:vs2) = zElem (zVar v1) (zVar v2) `blAnd` elms vs vs2
    elms _ _ = Top


uniqueness f = let ((trm, nm, rst), cond) = conditions f
                   trm2 = alt trm; cond2 = map alt cond
                   y = zVar "c"; y' = alt y; nf = norm "c" rst; -- a certain normalization to deal with variable names
                   vs = onlyFree 'c' [] trm; vs2 = onlyFree 'c' [] trm2
                   -- the following two parts specify the uniqueness formula. If the function is defined on a variable (and not on a term) we can significantly simplify it
                   ante = \f -> if isVar trm then mbAll (trName trm) . blImp (cnd cond `blAnd` domc nm trm) $ f  -- in this case we can significantly simplify the formula and do not need two kinds of variables
                                       else foldr mbAll (Imp (cnd cond `blAnd` cnd  cond2 `blAnd` (zEqu trm trm2) `And` domc nm trm `blAnd` pair trm) f) $ vs ++ vs2
                   post = zAll "c" $ zAll "c2" $ Imp (dive nf `And` dive (alt nf)) $ zEqu y y'
                   simp_post = if isVar trm then simp $ subst trm ("c2"++ tail (trName trm)) $ post else post -- here we reduce away the uniqueness task for those functions
                in Tag FUQ $ ante $ simp_post                                                                 -- that are defined by a term (possibly with choices)

  where
    cnd cond = foldr blAnd Top cond


    dive (And f g) = dive f `And` dive g
    dive (Imp f g) = f `Imp` dive g
    dive (Exi x f) = dive $ inst x f
    dive (Tag DEV (All x (Iff f g))) = dec $ inst x g
    dive (Tag _ f) = dive f
    dive f = f

    domc nm trm = zElem trm (zDom nm)

    pair t | isTrm t && trId t == pairId = pairAx
    pair _ = Top

    pairAx = let a = zVar "0"; b = zVar "1"; c = zVar "2"; d = zVar "3"
              in foldr zAll (Imp (zEqu (zPair a b) (zPair c d)) $ zEqu a c `And` zEqu b d) ["0","1","2","3"]

simp (All x f) = mbAll x $ simp $ inst x f
simp h@(Imp (And f g) _) = fromMaybe h $ do t1 <- getEq f; t2 <- getEq g; guard (closed t1 && twins t1 t2); return Top
  where
    getEq (Exi _ f) = getEq f
    getEq (And f g) = getEq f `mplus` getEq g
    getEq Trm {trName = "=" ,trArgs = [l,r]} | not (isInd l) && trName l `elem` ["c","c2"] =return r
    getEq _ = mzero




well_founded f = let ((trm, nm, rst), cond) = conditions f; vs = onlyFree 'c' [] trm
                     trm2 = alt trm; cond2 = map alt cond; vs2 = onlyFree 'c' [] trm2
                     nf = norm "" rst
                  in Tag FWF $ deC $ foldr zAll (foldr blAnd Top cond `blAnd` zElem trm (zDom nm) `blImp` (foldr And (less_def trm cond2 nm nf vs2 trm2) cond `blImp` recurse trm nm nf)) vs
  where
    less_def trm cond2 nm rst vs2 trm2 = zAll "" $ (zElem (zVar "") (zDom nm) `And` zLess (zVar "") trm) `Imp` foldr mbExi (foldr And (zEqu (zVar "") trm2 `And` app (alt rst)) cond2) vs2

    deC v@Var{trName = c:rst} | c == 'c' = v {trName = rst}
    deC (All (c:rst) f)       | c == 'c' = All rst f
    deC f = mapF deC f


    app = dive
      where
        dive (Imp f g) = f `Imp` dive g
        dive (And f g) = dive f `And` dive g
        dive (Exi x f) = Exi x $ dive f
        dive (Tag DEV (All x (Iff Trm {trArgs = [f,_]} g))) = dec $ subst f x $ inst x g
        dive (Tag _ f) = dive f
        dive f = f

    recurse trm nm  = foldr1 blAnd . map dive_al . deAnd
      where
        dive_al = dive . albet
        dive (And f g) = dive_al f `blAnd` (f `blImp` dive_al g)
        dive (Or  f g) = dive_al f `blAnd` (blNot f `blImp` dive_al g)
        dive (All x f) = blAll x $ dive_al f
        dive (Exi x f) = blAll x $ dive_al f
        dive (Tag DEV (All x (Iff Trm {trArgs = [f,_]} g))) = dec $ subst f x $ dive_al $ inst x g
        dive t@Trm{} = foldr blAnd Top $ map (flip zLess trm) $ reverse $ nubBy twins $ rc_list t
        dive (Tag _ f) = dive_al f
        dive (Not t) = dive t

        rc_list Trm{trArgs = args} = map (last .trArgs) (filter is_rec args) ++ concatMap rc_list args
        rc_list _ = []

        is_rec Trm{trId = tId, trArgs = [f',y]} = tId == appId && twins f' nm
        is_rec _ = False

property h = let (pr, fn) = prp h in Tag FPR $ blImp fn pr
  where
    prp (And f (And g (And (Tag DPR h) k))) = ( mb f `blAnd` h, zFun (head $ trArgs f) `And` (g `And` k))
    prp (And f (And g k)) | trId f == funId = (Top, Top)
                          | otherwise = (f, zFun (head $ trArgs f) `And` (g `And` k))

    mb t | isTrm t && trId t == funId = Top
         | otherwise = t

dmcnd (Tag _ (All _ (Iff Trm {trArgs = [_,dm]} g))) = dive
  where
    dive Trm {trId = tId, trArgs = [x,d]}
      | tId == elmId && twins d dm = subst x "" $ inst "" g
    dive f = mapF dive f




        --recurse trm nm rst = foldr zAll ()


alt v@Var {trName = 'c':nm} = v {trName = 'c':'2':nm}
alt (All ('c':nm) f) = All ('c':'2':nm) $ alt f
alt (Exi ('c':nm) f) = Exi ('c':'2':nm) $ alt f -- generate name variants
alt f = mapF alt f


norm y = dive
  where
    dive (Tag DEV (All x f)) = Tag DEV (All y f)
    dive (Tag DEV (Trm {trName = "=", trArgs = [f,t] }))
      = Tag DEV $ zAll y $ inc $ ( Iff (zEqu f vr) (zEqu vr t))
    dive f = mapF dive f

    vr = zVar y



-- notice that this takes place in the FM monad, therefore some lifts to get actions from the RM monad
getMacro cx tg = liftM (Tag tg . pd ) . either err return . dive
  where
    dive (And f g) = dive f `mplus` dive g
    dive (Imp f g) = liftM (Imp f) $ dive g
    dive (Tag tg' f) | tg == tg' = return $ tag tg f
    dive _ = Left $ "Warning: could not unfold macro: " ++ mcr tg

    err s = rlog (cnHead cx) s >> return Top

    pd (Imp f g) = Imp (Tag DIH f) g
    pd f = f                             -- so that an author may instantiate quantified variables

    mcr FDM = "domain"; mcr FEX = "existence"; mcr FUQ = "uniqueness"; mcr FWF = "wellfoundedness"; mcr FCH = "choices"


tag FWF  f = dive f
  where
    dive (All v f) = All v $ dive f
    dive (Imp f (Imp g h)) = Imp f (Imp (Tag DIH g) h)
tag FPR (Imp f g) = Imp (Tag DIH f) g
tag _  f= f
