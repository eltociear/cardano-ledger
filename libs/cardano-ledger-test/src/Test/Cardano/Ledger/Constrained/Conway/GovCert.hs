{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}

-- | Specs necessary to generate, environment, state, and signal
-- for the GOVCERT rule
module Test.Cardano.Ledger.Constrained.Conway.GovCert where

import Cardano.Ledger.CertState
import Cardano.Ledger.Conway.Governance
import Cardano.Ledger.Conway.PParams
import Cardano.Ledger.Conway.Rules
import Cardano.Ledger.Conway.TxCert
import qualified Data.Map as Map
import Lens.Micro

import Constrained

import Cardano.Ledger.Conway (ConwayEra)
import Cardano.Ledger.Crypto (StandardCrypto)
import Constrained.Base (Pred (Block))
import qualified Data.Set as Set
import Test.Cardano.Ledger.Constrained.Conway.Instances
import Test.Cardano.Ledger.Constrained.Conway.PParams

vStateSpec :: Specification fn (VState (ConwayEra StandardCrypto))
vStateSpec = TrueSpec

govCertSpec ::
  IsConwayUniv fn =>
  ConwayGovCertEnv (ConwayEra StandardCrypto) ->
  VState (ConwayEra StandardCrypto) ->
  Specification fn (ConwayGovCert StandardCrypto)
govCertSpec ConwayGovCertEnv {..} vs =
  let reps = Map.keysSet $ vsDReps vs
      -- deposits = lit [(k, drepDeposit dep) | (k, dep) <- Map.toList $ vsDReps vs]
      getNewMembers = \case
        UpdateCommittee _ _ newMembers _ -> Map.keysSet newMembers
        _ -> mempty
      knownColdCreds =
        Map.keysSet (foldMap committeeMembers cgceCurrentCommittee)
          <> foldMap (getNewMembers . pProcGovAction . gasProposalProcedure) cgceCommitteeProposals
      ccCertSpec coldCred = assert . member_ coldCred $ lit knownColdCreds
   in constrained $ \ [var|gc|] ->
        caseOn
          gc
          -- ConwayRegDRep
          ( branch $ \ [var|key|] [var|coinA|] _ ->
              [ not_ $ member_ key (lit reps)
              , coinA ==. lit (cgcePParams ^. ppDRepDepositL)
              ]
          )
          -- ConwayUnRegDRep
          ( if Set.null reps -- TODO Why does this branch "Fail"? shouldn't it just not generate a ConwayUnRegDRep certificate.
              then branch $ \_ _ -> True
              else branch $ \ [var|credB|] [var|coinB|] ->
                Block
                  [ assert $ member_ credB (lit reps)
                  , assert $ cJust_ coinB ==. lookup_ credB (lit (Map.map drepDeposit (vsDReps vs)))
                  ]
          )
          -- ConwayUpdateDRep
          ( branch $ \ [var|keyC|] _ -> member_ keyC (lit reps)
          )
          -- ConwayAuthCommitteeHotKey
          ( branch $ \ [var|coldCredD|] _ -> ccCertSpec coldCredD
          )
          -- ConwayResignCommitteeColdKey
          ( branch $ \ [var|coldCredE|] _ -> ccCertSpec coldCredE
          )

govCertEnvSpec ::
  IsConwayUniv fn =>
  Specification fn (ConwayGovCertEnv (ConwayEra StandardCrypto))
govCertEnvSpec =
  constrained $ \gce ->
    match gce $ \pp _ _ _ ->
      satisfies pp pparamsSpec
