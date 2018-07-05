{-
 -  ForTheL/Phrase.hs -- sentence grammar
 -  Copyright (c) 2001-2008  Andrei Paskevich <atertium@gmail.com>
 -
 -  This file is part of SAD/Alice - a mathematical text verifier.
 -
 -  SAD/Alice is free software; you can redistribute it and/or modify
 -  it under the terms of the GNU General Public License as published by
 -  the Free Software Foundation; either version 3 of the License, or
 -  (at your option) any later version.
 -
 -  SAD/Alice is distributed in the hope that it will be useful,
 -  but WITHOUT ANY WARRANTY; without even the implied warranty of
 -  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 -  GNU General Public License for more details.
 -
 -  You should have received a copy of the GNU General Public License
 -  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 -}

module Alice.ForTheL.Phrase where

import Control.Monad
import Data.List
import qualified Data.IntMap.Strict as IM
import Data.Maybe
import Data.Function

import Alice.Data.Base
import Alice.Data.Formula
import Alice.Data.Kit
import Alice.ForTheL.Base
import Alice.Parser.Prim
import Alice.Parser.Base

import Debug.Trace

-- Statement syntax

statement = headed -|- (aon_chain atomic >>= stail)

headed  = u1 -|- u2 -|- u3
  where
    u1  = liftM2 Imp (word "if" >> statement) (word "then" >> statement)
    u2  = liftM Not $ wrong >> statement
    u3  = liftM2 ($) qu_chain statement

stail x = opt x $ u1 -|- u2 -|- u3 -|- u4
  where
    u1  = liftM (And x) $ word "and" >> headed
    u2  = liftM (Or  x) $ word "or"  >> headed
    u3  = liftM (Iff x) $ iff >> statement
    u4  = do  wordOf ["when","where"]; y <- statement
              return $ foldr zAll (Imp y x) (decl [] y)

atomic  = atom -|- thereis -|- (wehve >> (smform -|- thesis))

smform  = liftM2 (flip ($)) s_form $ opt id qu_chain

thesis  = art >> (u1 -|- u2 -|- u3)
  where
    u1  = word "thesis" >> return zThesis
    u2  = word "contrary" >> return (Not zThesis)
    u3  = word "contradiction" >> return Bot

thereis = there >> (u1 -|- u2 -|- u3)
  where
    u1  = liftM hchain $ comma $ art >> notion
    u2  = do  word "no"; (q, f, v) <- notion
              return $ Not $ foldr mbExi (q f) v
    u3 = do (q, f, v) <- art >> word "unique" >> notion >>= single
            let vr = zVar v; vr' = zVar ""
            return $ mbExi v $ zAll "" (Iff (zEqu vr vr') $ subst vr' v $ q f)

    hchain ((q, f, v):ns) = foldr mbExi (bool $ And (q f) $ hchain ns) v
    hchain _  = Top

selection = liftM hchain $ comma $ art >> notion
  where
    hchain ((q, f, v):ns) = foldr xExi (bool $ And (q f) $ hchain ns) v
    hchain _  = Top

    xExi ('x':_) f = f
    xExi v f = mbExi v f

-- declarations

declaration = funDecl -|- setDecl

funDecl = symbFunDecl -|- wordFunDecl

wordFunDecl = do (q, f) <- optEx (id ,zFun zHole) $ wordOf ["a","an","the"] >> notion >>= single >>= \(q,f,v) -> return (q, subst zHole v f)
                 (cn, ph, vs, fn, t) <- wordHead; addDecl vs $
                  do def <- parenEx ld_body; (dom, st)  <- wordDom t
                     let df = defFun cn ph vs st def
                     return $ placeFun (substH fn $ q f) $ zFun fn `And` (Tag DDM (dom fn) `And` df fn)

wordDom s = do word "for"; (c, t) <- set_in False; guard $ twins t s
               st <- opt Top (word "where" >> statement)
               return (domFun c, st)

wordHead = do fvr <- var; char '['; t <- liftM snd fo_term; char ']' >> char '='
              h <- hidden; return (subst t h, zVar h, free [] t, zVar fvr, t)



symbFunDecl = do optEx () art; (q, f, v) <- (notion >>= single) -/- (do fvr <- var; return (id, zFun (zVar fvr), fvr)); char '=';
                 guard (not (null v) && head v == 'x')
                 let fn = zVar v
                 ap <- lambda ; return $ placeFun (q f) $ ap fn

placeFun Trm {trId = tId} f | tId == funId = f
placeFun t@Trm{} (And f g) = And t g
placeFun (And a b) (And f (And g h)) = And a (g `And` (Tag DPR b `And` h))



setDecl = do optEx () art; (q, f, v) <- (notion >>= single) -|- (do mvr <- var; return (id, zSet (zVar mvr), mvr)); char '=';
             guard (not (null v) && head v == 'x'); ap <- setEq False; let m = zVar v
             return $ place (q f) $ ap m
  where
    place Trm {trId = tId} f | tId == setId = f
    place t@Trm{} (And f g) = And t g
    place (And a b) (And f g) = And a (And g (Tag DPR b))


setEq p = do cnd <- setCond p; let v = zVar ""
             return $ \m -> (zSet m) `And` zAll "" (Iff (zElem v m) $ cnd v)

symbSetEq p = do cnd <- symbSet p; let v = zVar ""
                 return $ \m -> (zSet m) `And` zAll "" (Iff (zElem v m) $ cnd v)

setCond p = setTerm -|-symbSet p

symbSet p = cndSet p -|- finSet

setTerm = do t <- liftM snd fo_term; return $ \tr -> zElem tr t

cndSet p = exbrc $ do (c, t) <- set_in p; st <- (char '|' >> statement); dcl <- getDecl;
                      let vs = free dcl t
                      return $ \tr -> correct $ c tr `And` foldr mbExi (st `And` mbEqu tr t) vs
    where
      mbEqu u v@Var{} = zEqu v (zVar "")
      mbEqu t1 t2 = zEqu t1 t2
      correct (And (Tag DRP _) g) = Tag DRP g; correct f = bool f

finSet = exbrc $ do ts <- chain (char ',') ft;
                    return $ \tr -> foldr1 Or $ map (zEqu tr) ts
  where
    ft = liftM snd fo_term


set_in p = u1 -|- (if p then u2 else mzero)
  where
    u2 = do (q, f, v) <- notion >>= single; guard (not. isEqu $ f); return (\t -> subst t v $ q f, zVar v)
    u1 = do t <- ft; cnd <- opt drp (word "in" >> setCond p) ; return (cnd, t)
    drp = if p then const Top else Tag DRP
    ft = liftM snd fo_term


lambda = do (cn, ph, vs, dom, st) <- ld_head; addDecl vs $
              do def <- ld_body;
                 let dm = domFun dom; df = defFun cn ph vs st def
                 return $ \f -> zFun f `And` (Tag DDM (dm f) `And` df f)

defFun cn ph vs st def
      = \f -> foldr zAll (bool $ Imp st $ cn $ Tag DCD $ Imp (zElem ph $ zDom f) $ def ph f) vs
domFun dom = \f -> All "" $ Iff (zElem (Ind 0) $ zDom f) (dom $ Ind 0)

ld_head = dot $ char '\\' >> ld_dom

ld_dom = do (c, t)<- set_in False; (cn, ph) <- ld_var t; st <- opt Top (char ',' >> statement); return (cn, ph, free [] t, c, st)
  where
    err = "lambda head misformed"
    ld_var t = do h <- hidden; return $ (subst t h, zVar h)



ld_body = formula -|- cases
  where
    formula = do (y, st, chs) <- ld_statement; return $ \x f -> foldr ($) (mbIff y (zEqu (zApp f x) (zVar y)) st) chs
    cases   = do cas <- chain (char ',') ld_case;
                 return $ \x f -> foldr1 And $ map ( (&) f . (&) x ) cas

mbIff _ Trm {trName = "=", trArgs = [f,y]} Trm {trName = "=", trArgs = [y',t]}
      | twins y y' = Tag DEV $ zEqu f t
mbIff y f g = Tag DEV $ zAll y $ Iff f g


ld_case = do optEx () $ word "case"; cnd <- after statement arrow; (y, st, chs) <- ld_statement;
             return $ \x f -> Imp cnd $ foldr ($) (mbIff y (zEqu (zApp f x) (zVar y)) st) chs

ld_statement = do chs <- opt [] choices ; (y, st, ch) <- form -|- term -|- def_term; return (y, st , chs ++ ch)
  where
    form = liftM2 (\y st -> (y,st,[])) (after var $ such >> that) statement
    term  = do t <- liftM snd fo_term; h <- hidden; return (h, zEqu (zVar h) t, [])
    def_term = do ap <- symbSetEq False -|- lambda; hvr <- hidden; let h = zVar hvr; hvr2 = 'h':hvr
                  return $ (hvr2, zEqu (zVar hvr2) h, pure $ mbExi hvr . And (Tag DEF $ ap h))
    choices = after (chain (char ';') ld_choice) (word "in")

ld_choice = chc -|- def
  where
    chc = do word "choose"; (q, f, v) <- art >> notion >>= single; return $ zExi v . And (q f)
    def = do word "define"; fvr <- after var (char '='); let f = zVar fvr
             ap <- lambda -|- symbSetEq False;
             return $ zExi fvr . And (Tag DEF $ ap f)

arrow = char '-' >> char '>'


-- Set and function definitions

set_def = symb_set -|- set_of



set_of  = do sets; word "of"; (q, f, u) <- notion >>= single; h <- hidden; let v = zVar ""
             return (id, zSet zHole `And` zAll "" (Iff (zElem v zHole) $ subst v u $ q f), [h])

symb_set = do cnd <- symbSet True; h <- hidden; let v = zVar ""
              return (id, And (zSet zHole) (zAll "" (Iff (zElem v zHole) $ cnd v)), [h])

fun_def = do h <- hidden; ap <- lambda; return (id, ap zHole, [h])



-- Atomic syntax

atom :: FTL Formula
atom  = do  (q, ts) <- term_seq
            p <- and_chain does_literal
            liftM2 (q .) (opt id qu_chain) (dig p ts)

does_literal  = u1 -|- u2 -|- u3 -|- u4
  where
    u1  = does >> literal prim_ver
    u2  = does >> m_literal prim_m_ver
    u3  = has >> has_literal
    u4  = is >> and_chain (isa_literal -|- is_literal)

is_literal  = u1 -|- u2 -|- u3
  where
    u1  = literal prim_adj
    u2  = m_literal prim_m_adj
    u3  = with >> has_literal

isa_literal = u1 -|- u2
  where
    u1  = do  (q, f) <- anotion; return $ q f
    u2  = do  word "not"; (q, f) <- anotion; let unf = dig f [zHole]
              optEx (q $ Not f) $ liftM (q . Tag DIG . Not) unf

has_literal = u1 -|- u2 -|- u3 -|- u4
  where
    u1  = liftM (Tag DIG . hchain) (comma $ art >> possess)
    u2  = art >> word "common" >> liftM hchain (comma $ liftM digadd possess)
    u3  = do  word "no"; (q, f, v) <- possess
              return $ q $ Tag DIG $ Not $ foldr mbExi f v
    u4  = do  word "no"; word "common"; (q, f, v) <- possess
              return $ q $ Not $ foldr mbExi (Tag DIG f) v

    hchain ((q, f, v):ns) = q $ foldr mbExi (bool $ And f $ hchain ns) v
    hchain _  = Top

literal p   = positive p  -|- (word "not" >> negative p)
m_literal p = mpositive p -|- (word "not" >> mnegative p)
mpositive p = spositive p -|- (word "pairwise" >> ppositive p)
mnegative p = snegative p -|- (word "pairwise" >> pnegative p)

positive p  = do  (q, f) <- p term; return $ q $ Tag DIG f
spositive p = do  (q, f) <- p term; return $ q $ Tag DMS f
ppositive p = do  (q, f) <- p term; return $ q $ Tag DMP f

negative p  = do  (q, f) <- p term; return $ q $ Tag DIG $ Not f
snegative p = do  (q, f) <- p term; return $ q $ Not $ Tag DMS f
pnegative p = do  (q, f) <- p term; return $ q $ Not $ Tag DMP f


-- Notion syntax

anotion = art >> gnotion basentn rat >>= single >>= hol
  where
    hol (q, f, v) = return (q, subst zHole v f)
    rat = liftM (Tag DIG) stattr

notion  = gnotion (basentn -|- sym_notion) stattr >>= digntn

possess = gnotion (prim_of_ntn term) stattr >>= digntn

gnotion nt ra  =  do  ls <- liftM reverse la; (q, f, v) <- nt
                      rs <- opt [] $ liftM (:[]) (rc -|- ra)
                      return (q, foldr1 And $ f : ls ++ rs, v)
  where
    la  = opt [] $ liftM2 (:) lc la
    lc  = positive prim_un_adj -|- mpositive prim_m_un_adj
    rc  = and_chain is_literal -|- (that >> and_chain does_literal)

basentn = liftM digadd (prim_ntn term -|- cm -|- sym_eqnt  -|- set_def -|- fun_def)
  where
    cm  = word "common" >> prim_cm_ntn term term_seq

stattr  = such >> that >> statement

digadd (q, f, v)  = (q, Tag DIG f, v)

digntn (q, f, v)  = dig f (map zVar v) >>= \ g -> return (q, g, v)

single (q, f, [v])  = return (q, f, v)
single _            = nextfail "inadmissible multinamed notion"

-- Term syntax

term_seq :: FTL MTerm
term_seq  = liftM (foldl1 fld) $ comma mterm
  where
    fld (q, ts) (r, ss) = (q . r, ts ++ ss)

mterm :: FTL MTerm
mterm = qu_notion -|- liftM s2m nn_term
  where
    s2m (q, t) = (q, [t])

term :: FTL UTerm
term  = (qu_notion >>= m2s) -|- nn_term
  where
    m2s (q, [v]) = return (q, v)
    m2s _ = nextfail "inadmissible multinamed notion"

qu_notion :: FTL MTerm
qu_notion = paren (fa -|- ex -|- no)
  where
    fa  = do  wordOf ["every", "each", "all", "any"]; (q, f, v) <- notion
              return (q . flip (foldr zAll) v . blImp f, map zVar v)

    ex  = do  word "some"; (q, f, v) <- notion
              return (q . flip (foldr zExi) v . blAnd f, map zVar v)

    no  = do  word "no"; (q, f, v) <- notion
              return (q . flip (foldr zAll) v . blImp f . Not, map zVar v)

qu_chain  = liftM (foldl fld id) $ word "for" >> comma qu_notion
  where
    fld x (y, _)  = x . y

nn_term   = sym_term -|- paren (art >> prim_fun term)

fo_term   = sym_term -|- paren (art >> prim_fun fo_term)


-- Symbolic notation

sym_notion  = (paren (prim_snt s_term) -|- prim_tvr) >>= (digntn . digadd)

sym_eqnt    = do  t <- s_term; guard $ isTrm t
                  v <- hidden; return (id, zEqu zHole t, [v])

sym_term    = liftM ((,) id) s_term

variable    = liftM ((,) id) s_var

s_form  = liftM snd s_iff
  where
    s_iff = s_imp >>= bin_f Iff (string "<=>" >> s_imp)
    s_imp = s_dis >>= bin_f Imp (string "=>"  >> s_imp)
    s_dis = s_con >>= bin_f Or  (string "\\/" >> s_dis)
    s_con = s_una >>= bin_f And (string "/\\" >> s_con)
    s_una = s_all -|- s_exi -|- s_not -|- s_dot -|- s_atm
    s_all = liftM2 (qua_f zAll Imp) (string "forall" >> sym_notion) s_una
    s_exi = liftM2 (qua_f zExi And) (string "exists" >> sym_notion) s_una
    s_not = liftM (una_f Not) $ string "not" >> s_una
    s_dot = liftM ((,) False) $ char ':' >> s_form
    s_atm = liftM ((,) True)  $ s_atom

    una_f o (s, f)      = (s, o f)
    qua_f q o (_, f, v) = una_f $ flip (foldr q) v . o f

    bin_f o p r@(True, f) = opt r $ liftM (una_f $ o f) p
    bin_f _ _ r           = return r

    s_atom  = s_chain -|- prim_cpr s_term -|- set_macro -|- expar statement
    s_chain = liftM (foldl1 And . concat) s_hd

    s_ts    = chain (char ',') s_term                                 -- parse symbolic chains like equation chains
    s_hd    = l_hd -|- (s_ts >>= s_tl)
    s_tl ls = i_tl ls -|- r_tl ls

    l_hd    = do  pr <- prim_lpr s_term ; rs <- s_ts
                  liftM (map pr rs:) $ opt [] $ s_tl rs

    i_tl ls = do  pr <- prim_ipr s_term ; rs <- s_ts
                  let f = [ pr l r | l <- ls, r <- rs ]
                  liftM (f:) $ opt [] $ s_tl rs

    r_tl ls = do  pr <- prim_rpr s_term
                  return [map pr ls]

s_term    = i_term
  where
    i_term  = l_term >>= i_tl
    i_tl t  = opt t $ (prim_ifn s_term `ap` return t `ap` i_term) >>= i_tl

    l_term  = r_term -|- (prim_lfn s_term `ap` l_term)

    r_term  = c_term >>= r_tl
    r_tl t  = opt t $ (prim_rfn s_term `ap` return t) >>= r_tl

    c_term  = s_var -|- expar s_term -|- prim_cfn s_term

s_var     = liftM zVar var

set_macro = do t <- s_term; char '='; eq <- equ t; return $ zSet t `And` eq
  where
    equ t = do cnd <- symbSet True; let v = zVar ""
               return $ zAll "" (Iff (zElem v t) $ cnd v)


{-
-- Set notation

set_eqnt  = do  sets; v <- namlist; t <- set_of
                return (id, zEqu zHole t, v)

set_term  = sets >> namlist >> liftM ((,) id) set_of

set_of  = word "of" >> (u1 -|- u2 -|- u3)
  where
    u1  = notion >>= single >>= ntnset
    u2  = do t <- ft; s <- condn >> statement; trmset t s
    u3  = comma ft >>= finset
    ft  = liftM snd fo_term

set_strm  = exbrc (u1 -|- u2 -|- u3)
  where
    u1  = do  (q, f, v) <- notion >>= single
              s <- opt Top (char '|' >> statement)
              ntnset (q, bool $ And f s, v)
    u2  = do t <- ft; s <- (char '|' >> statement); trmset t s
    u3  = chain (char ',') ft >>= finset
    ft  = liftM snd fo_term

ntnset (q, f, v)  = retset v $ q f

trmset t s  = do  v <- hidden ; let u = zVar v
                  vs <- liftM (`decl` s) getDecl
                  retset v $ foldr mbExi (And s $ zEqu t u) vs

finset ts   = do  v <- hidden ; let u = zVar v
                  retset v $ foldl1 Or $ map (zEqu u) ts

retset v fe = do  (_:h) <- hidden ; let u = zVar v
                  mkElem <- getPattApp elemPat ntn_expr "elements not yet defined"
                  let ex = zAll v $ Iff (mkElem [u,zHole]) fe
                      nt = zSSS (- read h) h $ map zVar (free [] ex)
                  mkSet <- getPattApp setPat ntn_expr "sets not yet defined"
                  let nnt = nt {trInfo = [mkSet [ThisT]]}
                  return nnt
  where
    setPat = [Wd ["set"], Nm]
    elemPat = [Wd ["element"],Nm, Wd ["of"], Vr]
-}


-- Digger

dig f [_] | occursS f  = fail "too few subjects for an m-predicate"
dig f ts  = return (dive f)
  where
    dive (Tag DIG f)  = down (digS) f
    dive (Tag DMS f)  = down (digM $ zip ts $ tail ts) f
    dive (Tag DMP f)  = down (digM $ pairMP ts) f
    dive f  | isTrm f = f
    dive f  = mapF dive f

    down fn (And f g) = And (down fn f) (down fn g)
    down fn f         = foldl1 And (fn f)

    digS f  | occursH f = map (\ x -> substH x f) ts
            | otherwise = [f]

    digM ps f | not (occursS f) = digS f
              | not (occursH f) = map (\ y -> substS y f) $ tail ts
              | otherwise = map (\ (x,y) -> substS y $ substH x f) ps

    pairMP (t:ts) = [ (t, s) | s <- ts ] ++ pairMP ts
    pairMP _      = []


-- Chains

aon_chain p = (p >>= ao) -|- (word "neither" >> nr)
  where
    ao f  = liftM (foldl And f) (word "and" >> chain (word "and") p)
        -|- liftM (foldl Or  f) (word "or"  >> chain (word "or")  p)
        -|- return f
    nr    = liftM (foldl1 And . map Not) (chain (word "nor") p)

and_chain = liftM (foldl1 And) . chain (word "and")

comma = chain (word "and" -|- char ',')



-- Service stuff

has   = wordOf ["has", "have"]
with  = wordOf ["with", "of", "having"]
such  = wordOf ["such", "so"]
that  = wordOf ["that"]
sets  = wordOf ["set", "sets"]
does  = opt () $ wordOf ["does", "do"]
wehve = opt () $ word "we" >> word "have"
art   = opt () $ wordOf ["a", "an", "the"]
condn = (such >> that) -|- (word "provided" >> opt () that)
wrong = mapM_ word ["it","is","wrong","that"]
there = word "there" >> (is -|- wordOf ["exists","exist"])
iff   = mapM_ word ["if","and","only","if"] -|- word "iff"
stand = word "denote" -|- (word "stand" >> word "for")
