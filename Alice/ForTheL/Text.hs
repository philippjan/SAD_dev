{-
 -  ForTheL/Text.hs -- text grammar
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

module Alice.ForTheL.Text (forthel) where

import Control.Monad
import Data.List
import Data.Maybe
import qualified Data.IntMap.Strict as IM

import Alice.Data.Base
import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Text hiding (asm)
import Alice.ForTheL.Base
import Alice.ForTheL.Intro
import Alice.ForTheL.Phrase
import Alice.Parser.Base
import Alice.Parser.Prim
import Alice.Parser.Instr

import Debug.Trace

-- Top-level grammar

forthel = u1 -/- u2 -/- u3 -/- u5 -/- u6 -/- u7 -/- u8 -/- u4
  where
    u1  = liftM2 ((:).TB) topsent forthel
    u2  = liftM2 ((:).TB) (defsect -/- sigsect) forthel
    u3  = liftM2 ((:).TB) (axmsect -/- thmsect) forthel
    u4  = (alias -/- itvar -/- isyms) >> forthel
    u5  = (iexit -/- readEOI) >> return []
    u6  = liftM2 ((:).TI) iread (return [])
    u7  = liftM2 ((:).TI) instr forthel
    u8  = liftM2 ((:).TD) idrop forthel

axmsect = topsect Axiom axm axmaff
defsect = topsect Defn def define
sigsect = topsect Sign sig sigext
thmsect = topsect Theorem  thm (proof affirm)

topsect s h p =
    do  li <- nulText ; nm <- h
        tx <- getText ; bs <- tps
        la <- askPS psLang ; fn <- askPS psFile
        return $ Block zHole bs s [] nm [] la fn li tx
  where
    tps = u1 -/- u2 -/- u3 -/- u4
    u1  = assume >>= pretvr tps
    u2  = liftM2 ((:).TI) instr tps
    u3  = liftM2 ((:).TD) idrop tps
    u4  = p >>= \bl -> pretvr (return []) bl

topsent =
    do  li <- nulText ; bs@(TB bl:rs) <- pra
        la <- askPS psLang ; fn <- askPS psFile
        return $ if null rs then bl { blName = "" }
          else Block zHole bs Frame [] "" [] la fn li ""
  where pra = proof affirm >>= pretvr (return [])


-- Affirmations and selections with(out) a proof

data Scheme = Nul | Sht | Raw | InS | InT Formula | SIn | TIn String deriving Show

proof p = do  m1 <- shw; bl <- p
              let fr = blForm bl; modify = if blType bl == Declare && fun_tp fr then set_in_decl fr else id
              modify $
                  do  m2 <- prf; dvs <- getDecl
                      it <- imth m1 m2 >>= itrm fr
                      let ovs = free (blDecl bl ++ dvs) fr
                      nf <- iths fr it $ free (ovs ++ dvs) it
                      addDecl ovs $ body m1 m2 $ bl { blForm = nf }
  where
    body Nul Nul = return
    body _   Sht = prfsent
    body _   _   = prfsect

    imth (InT _) (InT _) = fail "conflicting induction schemes"
    imth m@(InT _) _  = return m ; imth _ m@(InT _)  = return m
    imth m@InS _      = return m ; imth _ m          = return m

    itrm _      (InT t) = return t
    itrm (All v _) InS  = return $ zVar v
    itrm _         InS  = fail "invalid induction thesis"
    itrm _ _            = return Top

    iths fr Top _       = return fr
    iths fr it vs       = liftM (iapp it) $ icnt vs fr
    iapp it cn          = cn $ Tag DIH $ substH it $ cn $ zLess it zHole

    icnt vs (Imp g f)   = liftM (Imp g .) $ icnt vs f
    icnt vs (All v f)   = liftM (zAll v .) $ icnt (delete v vs) f
    icnt [] f           = return (`Imp` f)
    icnt _ _            = fail "invalid induction thesis"

    fun_tp (Tag DCD _) = True
    fun_tp Trm{} = False
    fun_tp f = anyF fun_tp f


-- Proof schemes

shw = narrow $ optEx Nul $ letus >> dem >> after met that
prf = narrow $ optEx Nul $ sht -|- (word "proof" >> dot met)

sht = word "indeed" >> return Sht

met = opt Raw $ word "by" >> (u1 -|- u2 -|- u3 -|- u4)
  where
    u1  = word "contradiction" >> return Raw
    u2  = word "case" >> word "analysis" >> return Raw
    u3  = word "induction" >> opt InS (word "on" >> on)
    on  = liftM (InT . snd) fo_term
    u4 = word "structure" >> word "induction" >> opt SIn (word "on" >> sOn)
    sOn = liftM TIn var


-- Low-level sections: proofs, proof cases and frames

prfsent bl  = do  bs <- lowsent >>= pretvr (return [])
                  return bl { blBody = bs }

prfsect bl  = do  bs <- lowtext ; ls <- link
                  return bl { blBody = bs, blLink = blLink bl ++ ls }

lowtext = u1 -/- u2 -/- u3 -/- u4 -/- u5 -/- u6
  where
    u1  = lowsent >>= pretvr lowtext
    u2  = liftM2 ((:).TB) frame lowtext
    u3  = liftM2 ((:).TI) instr lowtext
    u4  = liftM2 ((:).TD) idrop lowtext
    u5  = qed >> return []
    u6  = castext

lowsent = assume -/- proof (affirm -/- choose -/- declre -/- decl_macro)

castext = u1
  where
    rst = u1 -/- u2 -/- u3 -/- u4
    u1  = liftM2 ((:).TB) cassect rst
    u2  = liftM2 ((:).TI) instr rst
    u3  = liftM2 ((:).TD) idrop rst
    u4  = qed >> return []

cassect = do  bl@(Block { blForm = fr }) <- cashyp
              prfsect $ bl { blForm = Imp (Tag DCH fr) zThesis }

frame   = do  li <- nulText ; nm <- frm
              tx <- getText ; bs <- dot lowtext
              la <- askPS psLang ; fn <- askPS psFile
              return $ Block zHole bs Frame [] nm [] la fn li tx


-- Sentences

choose  = sentence Select  (chs >> selection) asmvars link
cashyp  = sentence Case  (cas >> statement) rawvars link
affirm  = sentence Affirm  (aff >> statement) affvars link -/- eqchain
axmaff  = sentence Posit  (aff >> statement) affvars noln
assume  = sentence Assume (asm >> statement) asmvars noln
define  = sentence Posit definition defvars noln
sigext  = sentence Posit signaturex defvars noln
declre  = sentence Declare (dcl >> declaration) asmvars noln

sentence s pf pvars pl = narrow $
    do  na <- lowName; li <- nulText ; fr <- pf ; ls <- pl
        tx <- getText ; vs <- getDecl >>= pvars fr
        la <- askPS psLang ; fn <- askPS psFile; let nfr = rpObj fr
        return $ Block nfr [] s vs na ls la fn li tx

defvars f dvs | null xvs  = affvars f dvs
              | otherwise = nextfail err
  where
    xvs = filter (`notElem` free [] f) dvs
    err = "extra variables in the guard:" ++ sbs
    sbs = concatMap ((' ':) . show) xvs

asmvars f dvs = do  let nds = decl dvs f
                    affvars f $ nds ++ dvs
                    return nds

affvars f dvs = do  tvs <- askS $ concatMap fst . tvr_expr
                    let nvs = intersect tvs $ free dvs f
                    rawvars f $ dvs ++ nvs

rawvars f dvs = let wfc = overfree dvs f
                in  if null wfc then return [] else fail wfc


pretvr p bl = do  dvs <- getDecl; tvs <- askS tvr_expr
                  let bvs = blDecl bl
                      ovs = free (bvs ++ dvs) (blForm bl)
                      ofr = rpObj $ foldl1 And $ map (`gdc` tvs) ovs
                      obl = zbl { blForm = ofr, blDecl = ovs }
                  rst <- addDecl (ovs ++ bvs) $ liftM (TB bl :) p
                  return $ if (null ovs) then rst else TB obl : rst
  where
    gdc v = substH (zVar v) . snd . fromJust . find (elem v . fst)
    zbl   = bl { blBody = [], blType = Assume, blLink = [] }

rpObj t@Trm {trId = tId} | tId == objId = Top
                         | otherwise = t
rpObj (Iff f@(Tag DHD _) g) = Iff f $ rpObj g
rpObj (Imp f@(Tag DHD _) g) = Imp f $ rpObj g
rpObj f = bool $ mapF rpObj f
-- Macro in function declaration

decl_macro = ifM (askS in_decl) (domain -/- choices -/- existence -/- uniqueness -/- well_founded -/- property) mzero
  where
    domain = macro ["domain"] FDM; choices = macro ["choice", "choices"] FCH
    existence = macro ["existence"] FEX; uniqueness = macro ["uniqueness"] FUQ
    well_founded = macro ["wellfoundedness"] FWF; property = macro ["property"] FPR

    macro ss tg = do li <- nulText; wordOf ss >> char '.'; la <- askPS psLang; fn <- askPS psFile; tx <- getText
                     return $ Block (Tag tg zHole) [] Affirm [] "__" [] la fn li tx

-- Service stuff

noln  = dot $ return []
link  = dot $ opt [] $ expar $ word "by" >> chain (char ',') readTkLex
hdr p = dot $ p >> opt "" readTkLex

axm = hdr $ word "axiom"
def = hdr $ word "definition"
sig = hdr $ word "signature"
thm = hdr $ wordOf ["theorem", "lemma", "corollary", "proposition"]
frm = hdr $ wordOf ["part", "block", "frame"]

dem = wordOf ["prove", "show", "demonstrate"]
qed = wordOf ["end", "qed", "trivial", "obvious"]

cas = word "case"
asm = word "let" -|- lus
lus = letus >> wordOf ["assume", "presume", "suppose"] >> opt () that
chs = hence >> letus >> wordOf ["choose", "take", "consider"]
aff = hence
dcl = word "define"

letus  = opt () $ (word "let" >> word "us") -|- (word "we" >> word "can")
hence  = opt () $ wordOf ["then", "hence", "thus", "therefore"]







-- equality chains




eqchain = do na <- lowName; li <- nulText; eqs <- dot eq_chain; tx <- getText
             la <- askPS psLang; fn <- askPS psFile; f <- bf eqs
             let bs = map (makeBlock la fn) eqs
             getDecl >>= affvars (foldl1 And (map (fst . fst) eqs))
             return $ Block f bs Affirm [] na [] la fn li tx
  where
    bf fs = do let (Tag DEC Trm {trArgs = [t,_]}) = (fst . fst . head) fs
                   (Tag DEC Trm {trArgs = [_,s]}) = (fst . fst . last) fs
               return $ Tag DEC $ zEqu t s
    makeBlock la fn ((f, ln), li) = TB $ Block f [] Affirm [] "__" ln la fn li (show f)

eq_chain = do t <- s_term
              eq_ch t
    where
      eq_ch t = do li <- nulText; string ".="; s <- s_term; ln <- eqlink
                   liftM ((:) ((Tag DEC (zEqu t s), ln) , li)) $ opt [] $ eq_ch s

      eqlink = opt [] $ expar $ word "by" >> chain (char ',') readTkLex



---- lowName

lowName = opt "__" $ expar readTkLex
