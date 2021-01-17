{- | This module provides a variant of `ghc-typelits-presburger`,
 which can be also solve symbols added in this package, such as
 @Min@, @Max@, @<@, @>@, and @>=@.
-}
module Data.Type.Natural.Presburger.MinMaxSolver (plugin) where

import Control.Monad (mzero)
import GHC.TypeLits.Presburger.Compat (lookupModule)
import GHC.TypeLits.Presburger.Types
import GhcPlugins
  ( Plugin,
    fsLit,
    mkModuleName,
    mkTcOcc,
    splitTyConApp_maybe,
  )
import TcPluginM

plugin :: Plugin
plugin =
  pluginWith $
    (<>) <$> defaultTranslation <*> genTypeNatsTranslation

genTypeNatsTranslation :: TcPluginM Translation
genTypeNatsTranslation = do
  orderMod <- lookupModule (mkModuleName "Data.Type.Natural.Lemma.Order") (fsLit "type-natural")
  singNatLt <- tcLookupTyCon =<< lookupOrig orderMod (mkTcOcc "<?")
  singNatGeq <- tcLookupTyCon =<< lookupOrig orderMod (mkTcOcc ">=?")
  singNatGt <- tcLookupTyCon =<< lookupOrig orderMod (mkTcOcc ">?")

  singNatLtProp <- tcLookupTyCon =<< lookupOrig orderMod (mkTcOcc "<")
  singNatGeqProp <- tcLookupTyCon =<< lookupOrig orderMod (mkTcOcc ">=")
  singNatGtProp <- tcLookupTyCon =<< lookupOrig orderMod (mkTcOcc ">")

  singMin <- tcLookupTyCon =<< lookupOrig orderMod (mkTcOcc "Min")
  singMax <- tcLookupTyCon =<< lookupOrig orderMod (mkTcOcc "Max")
  caseMinAux <- tcLookupTyCon =<< lookupOrig orderMod (mkTcOcc "MinAux")
  caseMaxAux <- tcLookupTyCon =<< lookupOrig orderMod (mkTcOcc "MaxAux")
  return
    mempty
      { natGeqBool = [singNatGeq]
      , natLtBool = [singNatLt]
      , natGtBool = [singNatGt]
      , natMin = [singMin]
      , natMax = [singMax]
      , parsePred = \toE ty ->
          case splitTyConApp_maybe ty of
            Just (con, [l, r])
              | con == singNatLtProp -> (:<) <$> toE l <*> toE r
              | con == singNatGtProp -> (:>) <$> toE l <*> toE r
              | con == singNatGeqProp -> (:>=) <$> toE l <*> toE r
            _ -> mzero
      , parseExpr = \toE ty ->
          case splitTyConApp_maybe ty of
            Just (con, [_, n, m])
              | con == caseMinAux ->
                Min <$> toE n <*> toE m
              | con == caseMaxAux ->
                Max <$> toE n <*> toE m
            _ -> mzero
      }
