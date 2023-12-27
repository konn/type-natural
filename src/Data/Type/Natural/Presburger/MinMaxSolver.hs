{-# LANGUAGE CPP #-}

{- | This module provides a variant of `ghc-typelits-presburger`,
 which can be also solve symbols added in this package, such as
 @Min@, @Max@, @<@, @>@, and @>=@.
-}
module Data.Type.Natural.Presburger.MinMaxSolver (plugin) where

import Control.Monad (mzero)
import GHC.TypeLits.Presburger.Compat
import GHC.TypeLits.Presburger.Types

import GHC.Plugins
  ( Plugin,
    fsLit,
    mkModuleName,
    mkTcOcc,
    splitTyConApp_maybe,
  )
import GHC.Tc.Plugin

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
#if !MIN_VERSION_ghc(9,2,1)
  ordCondTyCon <- tcLookupTyCon =<< lookupOrig orderMod (mkTcOcc "OrdCond")
#endif
  return
    mempty
      { natGeqBool = [singNatGeq]
      , natLtBool = [singNatLt]
      , natGtBool = [singNatGt]
      , natMin = [singMin]
#if !MIN_VERSION_ghc(9,2,1)
      , ordCond = [ordCondTyCon]
#endif
      , natMax = [singMax]
      , parsePred = \toE ty ->
          case splitTyConApp_maybe ty of
            Just (con, [l, r])
              | con == singNatLtProp -> (:<) <$> toE l <*> toE r
              | con == singNatGtProp -> (:>) <$> toE l <*> toE r
              | con == singNatGeqProp -> (:>=) <$> toE l <*> toE r
            _ -> mzero
      }
