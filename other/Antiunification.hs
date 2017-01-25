{-# LANGUAGE OverloadedStrings, FlexibleInstances #-}
module Antiunification where
import Control.Monad.State.Lazy
import qualified Data.Bimap as M
import qualified PGF as P
import PGF.Expr
import PGF.CId (CId(..))
import Data.ByteString.Char8 (unpack, isSuffixOf)
import Data.List (intercalate)

import Data.Set (Set, union, singleton, empty)

data Term v f = Var v
                | App f [Term v f]
                deriving (Eq, Ord)

instance Show v => Show (Term v String) where
  show (Var v)    = "#" ++ show v
  show (App f xs) | null xs = f
                  | otherwise = "(" ++ f ++ " " ++ intercalate " " (map show xs) ++ ")"

type Vary v f = Term v f -> Term v f -> v


lgg :: (Ord f, Eq f) => T f -> T f ->  (T f, Subs Int f)
lgg  a b = runState (do
      s <- get
      let (s',t) = lgg' s (a, b)
      put s'
      return t) sinit

data Subs v f = S { subs :: M.Bimap v (Term v f,Term v f),
                    next :: v }

supdate :: (Enum v, Ord f, Ord v) => Subs v f -> (Term v f, Term v f) -> Subs v f
supdate s@(S m n) ts =
  case M.lookupR ts m of
    Nothing ->  S (M.insert n ts m) (succ n)
    _       -> s

sinit :: Subs Int f
sinit = S M.empty 0


lgg' :: (Ord v, Ord f, Enum v, Eq f) => Subs v f -> (Term v f, Term v f) -> (Subs v f, Term v f)
lgg' m (App f xs, App g ys) | f == g && length xs == length ys = (m', App f args)
  where
    (m', args) = foldl (\(m,ts) xy -> let (m', t')  = lgg' m xy
                                      in (m', t':ts)) (m, []) $ zip xs ys
lgg' m st = let m' = supdate m st
                v = (subs m') M.!> st
             in (m', Var v)

type T a = Term Int a



depth :: P.Expr -> Int
depth (EAbs _ _ e) = 1 + depth e
depth (EApp e1 e2) = 1 + max (depth e1) (depth e2)
depth (ETyped e _) = depth e
depth (EImplArg e) = depth e
depth _            = 1


getLexical :: P.Expr -> Set P.Expr
getLexical (EAbs _ _ e) = getLexical e
getLexical (EApp e1 e2) = getLexical e1 `union` getLexical e2
getLexical e@(ELit l)   = singleton e
getLexical (ETyped e _) = getLexical e
getLexical e@(EFun c) | isLexical c =  singleton e
  where isLexical :: CId -> Bool
        isLexical (CId c) = any (flip isSuffixOf c) ["_A", "_N"]
getLexical (EImplArg e) = getLexical e
getLexical _            = empty

convert :: P.Expr -> T String
convert (EApp e1 e2) = App "EApp" $ map convert [e1, e2]
convert (EFun (CId s)) = App (unpack s) []
convert (ELit s) = App (case s of
                     LStr s -> s
                     LInt n -> show n
                     LFlt x -> show x) []

main = do
  putStrLn "Reading PGF..."
  pgf <- P.readPGF "./App.pgf"
  putStrLn "done"
  let eng = P.mkCId "AppEng"
      Just tp = P.readType "Cl"
      ps = P.parse pgf eng tp "2 is prime"
  return $  map convert  ps
