{-# LANGUAGE TemplateHaskell #-}
-- | Re-exports arithmetic and order structure for peano arithmetic.
module Data.Type.Natural.Class
       ( module Data.Type.Natural.Class.Arithmetic
       , module Data.Type.Natural.Class.Order
       , -- * Quasi quoters generator for naturals
         mkSNatQQ) where
import Data.Type.Natural.Class.Arithmetic
import Data.Type.Natural.Class.Order

import Data.Singletons.Prelude   (FromInteger, Sing, sing)
import Language.Haskell.TH       (ExpQ, TypeQ, litT, numTyLit, sigT)
import Language.Haskell.TH.Quote (QuasiQuoter (..))

-- | Quasiquoter generateor for specific peano-types.
--
--   Since 0.7.0.0
mkSNatQQ :: TypeQ -> QuasiQuoter
mkSNatQQ t = QuasiQuoter
             { quoteExp = mkExpQuote
             , quotePat = error  "no pattern quoter for snats"
                          -- foldr (\a b -> conP a [b]) (conP 'SZ []) . flip replicate 'SS . read
             , quoteType = mkTypeQuote
             , quoteDec = error "not implemented"
             }
  where
    mkExpQuote ::  String -> ExpQ
    mkExpQuote s = [| sing :: $(mkTypeQuote s) |]

    mkTypeQuote :: String -> TypeQ
    mkTypeQuote s =
      let n = read s
      in [t| Sing $(sigT [t| FromInteger $(litT $ numTyLit n)|]  =<< t) |]
