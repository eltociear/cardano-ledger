{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

module Test.Cardano.Ledger.Constrained.Conway.PParams where

import Cardano.Ledger.BaseTypes
import Cardano.Ledger.Conway.Core
import Constrained
import Test.Cardano.Ledger.Constrained.Conway.Instances (
  EraPP (..),
  IsConwayUniv,
  SimplePParams (..),
 )

-- ==========================================================

-- | A Spec for SimplePParams, which we will lift to a Spec on PParams
simplePParamsSpec :: IsConwayUniv fn => Specification fn SimplePParams
simplePParamsSpec = constrained $ \simplepp ->
  match simplepp $
    \_minFeeA
     _minFeeB
     maxBBSize
     maxTxSize
     maxBHSize
     _keyDeposit
     poolDeposit
     eMax
     _nOpt
     _a0
     _rho
     _tau
     _decentral
     protocolVersion
     _minUTxOValue
     _minPoolCost
     -- Alonzo
     _coinsPerUTxOWord
     costModels
     _prices
     _maxTxExUnits
     _maBlockExUnits
     maxValSize
     collateralPercentage
     _MaxCollateralInputs
     -- Babbage
     _coinsPerUTxOByte
     -- Conway
     _poolVotingThresholds
     _drepVotingThresholds
     _committeeMinSize
     committeeMaxTermLength
     govActionLifetime
     govActionDeposit
     dRepDeposit
     _drepActivity
     _minFeeRefScriptCostPerByte ->
        [ assert $ protocolVersion ==. lit (ProtVer (natVersion @10) 0)
        , assert $ maxBBSize /=. lit 0
        , assert $ maxTxSize /=. lit 0
        , assert $ maxBHSize /=. lit 0
        , assert $ maxValSize /=. lit 0
        , assert $ collateralPercentage /=. lit 0
        , assert $ committeeMaxTermLength /=. lit (EpochInterval 0)
        , assert $ govActionLifetime /=. lit (EpochInterval 0)
        , assert $ poolDeposit /=. lit mempty
        , assert $ govActionDeposit /=. lit mempty
        , assert $ dRepDeposit /=. lit mempty
        , match eMax $ \epochInterval -> lit 0 <. epochInterval
        , assert $ costModels ==. lit mempty -- This makes examples soo much more readable.
        ]

pparamsSpec :: (EraPP era, IsConwayUniv fn) => Specification fn (PParams era)
pparamsSpec =
  constrained $ \pp ->
    match pp $ \simplepp -> [satisfies simplepp simplePParamsSpec]
