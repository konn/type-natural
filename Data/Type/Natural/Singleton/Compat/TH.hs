{-# LANGUAGE TemplateHaskell #-}
module Data.Type.Natural.Singleton.Compat.TH where
import Control.Applicative ((<|>))
import Control.Monad       (forM, zipWithM)
import Data.Maybe          (fromMaybe)
import Data.Singletons
import Language.Haskell.TH

generateCompat :: Maybe Fixity -> Name -> String -> DecsQ
generateCompat mfix cls opname = do
  mfix' <- reifyFixity (mkName opname)
  Just oldOpName <- lookupTypeName  $ ":" ++ opname
  Just oldSingName <- lookupValueName $ "%:" ++ opname
  Just oldCur1Name <- lookupTypeName  $ ":" ++ opname ++ "$"
  Just oldCur2Name <- lookupTypeName  $ ":" ++ opname ++ "$$"
  Just oldCur3Name <- lookupTypeName  $ ":" ++ opname ++ "$$$"
  let newOpName = mkName opname
      newSingName = mkName $ "%" ++ opname
      newCur1Name = mkName $ opname ++ "@#@$"
      newCur2Name = mkName $ opname ++ "@#@$$"
      newCur3Name = mkName $ opname ++ "@#@$$$"
  cur12 <- zipWithM (\old new -> tySynD new [] (conT old))
           [oldCur1Name, oldCur2Name]
           [newCur1Name, newCur2Name]
  [a, b] <- mapM newName ["a", "b"]
  cur3 <- tySynD newCur3Name (map PlainTV [a,b])
          $ infixT (varT a) oldCur3Name (varT b)
  nat <- newName "nat"
  tysyn <- tySynD newOpName [PlainTV a, PlainTV b] $
           infixT (varT a) oldOpName (varT b)
  sig <- sigD newSingName $
         forallT [PlainTV nat, KindedTV a (VarT nat), KindedTV b (VarT nat)]
         (sequence [[t| $(conT cls) $(varT nat) |]])
         [t| Sing $(varT a) -> Sing $(varT b) -> Sing $(infixT (varT a) newOpName (varT b)) |]
  defn <- funD newSingName [clause [] (normalB $ varE oldSingName) [] ]
  fixes <- fmap (fromMaybe []) $ forM (mfix <|> mfix') $ \fixity ->
    return [InfixD fixity newOpName, InfixD  fixity newSingName]
  return (sig : defn : tysyn : cur12 ++ [cur3] ++ fixes)

