{-#  LANGUAGE GADTs, KindSignatures, LambdaCase,
     TypeOperators, MultiParamTypeClasses,
     FlexibleInstances, ExistentialQuantification #-}

module Main where
import PGF.Expr
import PGF hiding (Type)
import qualified PGF as P
import PGF.CId
import PGF.ByteCode()
import Data.Generic.Diff
import System.IO
import qualified Data.ByteString.Char8 as BS
import System.Process


data TreeFamily :: * -> * -> * where
  EVar' :: TreeFamily Tree Nil -- (Cons Int Nil)
  ETyped' :: TreeFamily Tree (Cons Tree Nil) -- (Cons P.Type Nil))
  EFun' :: TreeFamily Tree Nil -- (Cons CId  Nil)
  EApp' :: TreeFamily Tree (Cons Tree (Cons Tree Nil))
  ELit' :: TreeFamily Tree Nil -- (Cons Literal Nil)
  EMeta' :: TreeFamily Tree Nil -- (Cons MetaId Nil)
  EImplArg' :: TreeFamily Tree (Cons Tree Nil)
  --Explicit' :: TreeFamily BindType Nil
  --Implicit' :: TreeFamily BindType Nil
  --Int'      :: Int -> TreeFamily Int Nil
  --Double'   :: Double -> TreeFamily Double Nil
  -- String'   :: String -> TreeFamily String Nil
  --CId'      :: TreeFamily CId Nil -- (Cons BS.ByteString Nil)
  --ByteString' :: BS.ByteString -> TreeFamily BS.ByteString Nil
  --LStr' :: TreeFamily Literal (Cons String Nil)
  --LInt' :: TreeFamily Literal (Cons Int Nil)
  --LFlt' :: TreeFamily Literal (Cons Double Nil)
  EAbs' :: TreeFamily Tree (Cons Tree Nil)
  -- DTyp' :: TreeFamily P.Type (Cons [Hypo] (Cons CId (Cons [Tree] Nil)))

instance Family TreeFamily where
  decEq EVar'  EVar'  = Just (Refl, Refl)
  decEq ETyped' ETyped'  = Just (Refl, Refl)
  decEq EApp'  EApp'  = Just (Refl, Refl)
  decEq EFun'  EFun'  = Just (Refl, Refl)
  decEq ELit'  ELit'  = Just (Refl, Refl)
  decEq EMeta' EMeta' = Just (Refl, Refl)
  --decEq LStr' LStr'   = Just (Refl, Refl)
  --decEq LInt' LInt'   = Just (Refl, Refl)
  --decEq LFlt' LFlt'   = Just (Refl, Refl)
  decEq EAbs'  EAbs'  = Just (Refl, Refl)
  {- decEq (Int' x) (Int' y) | x == y     = Just (Refl, Refl)
    | otherwise                       = Nothing
   decEq (Double' x) (Double' y) | x == y     = Just (Refl, Refl)
   | otherwise                       = Nothing
  decEq (ByteString' a) (ByteString' b) | a == b  = Just (Refl, Refl)
    | otherwise                          = Nothing
  decEq (String' a) (String' b) | a == b  = Just (Refl, Refl)
    | otherwise = Nothing
    -}
  decEq _      _      = Nothing

  fields EVar' (EVar i)     = Just CNil -- (CCons i CNil)
  fields EFun' (EFun c)  = Just CNil -- (CCons c CNil)
  fields EApp' (EApp f x)  = Just (CCons f (CCons x CNil))
  fields ELit' (ELit l)     = Just CNil -- (CCons l CNil)
  fields EMeta' (EMeta m)   = Just CNil -- (CCons m CNil)
  fields EAbs' (EAbs b c t) = Just (CCons t CNil)
  fields ETyped' (ETyped e t) = Just (CCons e CNil)
  fields EImplArg' (EImplArg e) = Just (CCons e CNil)
  --fields Explicit' _        = Just CNil
  --fields Implicit' _        = Just CNil
  --fields (Int' _)  _        = Just CNil
  --fields (Double' _)  _     = Just CNil
  --fields (String' _)  _     = Just CNil
  --fields CId' (CId bs)      =  Just CNil -- (CCons bs CNil)
  --fields LStr' (LStr s)     = Just (CCons s CNil)
  --fields LInt' (LInt i)     = Just (CCons i CNil)
  --fields LFlt' (LFlt x)     = Just (CCons x CNil)
  --fields f      args        = error $ "No field for " ++ string f
  fields _ _ = Nothing

  apply EVar' CNil                       = EVar 0
  apply EFun'  CNil                      = EFun undefined
  apply EApp' (CCons f (CCons x CNil))   = EApp f x
  apply ELit' CNil                       = ELit undefined
  apply ETyped' (CCons e CNil)           = ETyped e undefined
  apply EMeta' CNil                      = EMeta undefined
  apply EImplArg' (CCons e CNil)         = EImplArg e
  --apply Explicit' _                     = Explicit
  --apply Implicit' _                     = Implicit
  --apply (Int' i) CNil                   = i
  apply EAbs' (CCons t CNil) = EAbs undefined undefined t
  --apply (Double' x) CNil                = x
  --apply (String' s) CNil                = s
  --apply LStr' (CCons s CNil)            = LStr s
  --apply LInt' (CCons i CNil)            = LInt i
  --apply LFlt' (CCons x CNil)            = LFlt x

  string EAbs' = "Abs"
  string EVar' = "Var"
  string EApp' = "App"
  string ETyped' = "Typed"
  string EFun' = "Fun"
  string ELit' = "Lit"
  string EMeta' = "Meta"
  string _ = undefined



instance Type TreeFamily Expr where
  constructors = [Concr EApp', Concr ETyped', Concr ELit', Concr EFun', Concr EMeta', Concr EAbs', Concr EVar', Concr EImplArg']

{-instance Type TreeFamily Int where
  constructors = [Abstr Int']

instance Type TreeFamily CId where
  constructors = [Concr CId']

instance Type TreeFamily BS.ByteString where
  constructors = [Abstr ByteString']

instance Type TreeFamily Literal where
  constructors = [Concr LStr', Concr LInt', Concr LFlt']
instance Type TreeFamily Double where
  constructors = [Abstr Double']

instance Type TreeFamily String where
  constructors = [Abstr String']

instance Type TreeFamily BindType where
  constructors = [Concr Explicit', Concr Implicit']

instance Type TreeFamily P.Type where
  constructors = [Concr DTyp']
-}

distance :: Expr -> Expr -> Int
distance a b = dist dab  where
  dab :: ES
  dab = diff a b
  dist ::  forall f txs tys . EditScriptL f txs tys -> Int
  dist (CpyTree a) = dist a
  dist (Cpy _ bs)  = dist bs
  dist (Ins _ bs) = 1 + dist bs
  dist (Del _ bs) = 1 + dist bs
  dist End        = 0

type ES = EditScript TreeFamily Expr Expr

view :: PGF -> Language -> String -> Tree -> IO ()
view pgf lang name exp = do
  let gv = graphvizParseTree pgf lang graphvizDefaults exp
      pngPath = name ++ ".png"
  readCreateProcess  (shell $ "dot -Tpng -o " ++ pngPath) gv
  putStrLn $ "Wrote " ++ pngPath


main :: IO ()
main = do
  putStr "Reading PGF..."
  hFlush stdout
  pgf <- readPGF "./App.pgf"
  putStrLn "done"
  let eng = mkCId "AppEng"
      Just tp = readType "Cl"
      ps = parse pgf eng tp "2 is prime" :: [Expr]
      eps = zip ['a'..] ps :: [(Char,Expr)]
  mapM_ (\(i,a) -> view pgf eng [i] a) eps
  mapM_ (\(i,x) -> putStr (i:": ") >> print x)  eps
  mapM_ (\((i,a),(j,b)) -> do
    putStr $ "(" ++ [i] ++ "," ++ [j] ++ "): "
    let dab = diff a b :: ES
    print $ distance a b) . filter (uncurry (<)) . concat $ [[(ia, ib) | ib <- eps] | ia <- eps]

  let a = ps !! 0
      c = ps !! 2
      dac = diff a c :: ES
      c'  = patch dac a
  print  $ dac
  print $ distance c c'
