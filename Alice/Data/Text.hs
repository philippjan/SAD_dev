{-
 -  Data/Text.hs -- block and text datatypes and core functions
 -  Copyright (c) 2001-2008  Andrei Paskevich <atertium@gmail.com>
 -
 -  This file is part of SAD/Alice - a mathematical text verifier.
 -
 -  SAD/Alice is free software; you can redistribute it and/or modify
 -  it launchunder the terms of the GNU General Public License as published by
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

module Alice.Data.Text where

import Data.List

import Alice.Data.Base
import Alice.Data.Formula
import Alice.Data.Instr
import Alice.Data.Kit
import Debug.Trace

data Text = TB Block | TI Instr | TD Idrop

data Block  = Block { blForm :: Formula,  blBody :: [Text],   -- Formula image / body of the block
                      blType :: Section,  blDecl :: [String], -- block type / variables declared in the block
                      blName :: String,   blLink :: [String], -- identifier of the block / proof link provided in the block ("by" statement)
                      blLang :: String,   blFile :: String,   -- language the block is written in (i.e. forthel, tptp) / file the block came from
                      blLine :: Int,      blText :: String }  -- line number / text of that block

data Context  = Context { cnForm :: Formula,  -- formula of the context
                          cnBran :: [Block],  -- branch of the context
                          cnMESN :: [MRule],  -- MESON rules extracted from the formula
                          cnRedu :: Formula } -- ontologically reduced formula
data MRule = MR { asm :: [Formula], -- assumptions of the rule
                  conc :: Formula } -- conclusion of the rule
                    deriving Show



{- All possible types that a ForThel block can have. -}
data Section = Defn | Sign | Axiom | Theorem | Case | Assume | Select | Affirm | Posit | Frame | Declare deriving Eq

{- necessity of proof as derived from the block type -}
blSign bl = sign $ blType bl
  where
    sign Defn = False
    sign Sign = False
    sign Axiom = False
    sign Assume = False
    sign Declare = True
    sign _ = True

isDecl = (==) Declare . blType


-- Block utilities

noForm :: Block -> Bool
noForm  = isHole . blForm

noBody :: Block -> Bool
noBody  = null . blBody

getBlock :: Text -> Block
getBlock (TB bl) = bl


-- Composition

{- form the formula image of a whole block -}
formulate :: Block -> Formula
formulate bl  | noForm bl = compose $ blBody bl
              | otherwise = blForm bl

compose :: [Text] -> Formula
compose tx = foldr comp Top tx
  where
    comp (TB bl@(Block{ blDecl = dvs })) fb
      | blSign bl || blType bl == Defn = foldr zExi (bool $ And (formulate bl) fb) dvs
      | otherwise = foldr zAll (bool $ Imp (formulate bl) fb) dvs
    comp _ fb = fb



-- Context utilities

cnHead  = head . cnBran
cnTail  = tail . cnBran
cnTopL  = null . cnTail                     -- Top Level context
cnLowL  = not  . cnTopL                     -- Low Level context

cnSign  = blSign . cnHead
cnDecl  = blDecl . cnHead
cnName  = blName . cnHead
cnLink  = blLink . cnHead

isAssm = (==) Assume . blType . cnHead

setForm :: Context -> Formula -> Context
setForm cx fr = cx { cnForm = fr }

setRedu :: Context -> Formula -> Context
setRedu cx fr = cx { cnRedu = fr }



-- Show instances

instance Show Text where
  showsPrec p (TB bl) = showsPrec p bl
  showsPrec 0 (TI is) = showsPrec 0 is . showChar '\n'
  showsPrec 0 (TD is) = showsPrec 0 is . showChar '\n'
  showsPrec _ _ = id

instance Show Block where
  showsPrec p bl  | noBody bl = showForm p bl
                  | noForm bl = showForm p bl . sbody
                  | otherwise = showForm p bl
                              . showIndent p . showString "proof.\n"
                              . sbody
                              . showIndent p . showString "qed.\n"
    where
      sbody = foldr ((.) . showsPrec (succ p)) id $ blBody bl

showForm p bl = showIndent p . sform (noForm bl) (blSign bl) . dt
  where
      sform True  True  = showString $ "conjecture" ++ mr
      sform True  False = showString $ "hypothesis" ++ mr
      sform False False = showString "assume " . shows fr
      sform False True  = shows fr

      mr = if null nm then "" else (' ':nm)
      fr = blForm bl ; nm = blName bl
      dt = showString ".\n"

showIndent :: Int -> ShowS
showIndent n  = showString $ replicate (n * 2) ' '




----- only for debugging purposes

instance Show Context where
    show cnt = showString "cnForm : " . showString (show $ cnForm cnt) $ ""
