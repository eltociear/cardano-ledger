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
import qualified Data.Map.Strict as Map
import Lens.Micro

import Constrained

import Cardano.Ledger.Conway (ConwayEra)
import Cardano.Ledger.Crypto (StandardCrypto)
import Constrained.Base (Pred (..))
import Test.Cardano.Ledger.Constrained.Conway.Instances
import Test.Cardano.Ledger.Constrained.Conway.PParams

{-

import qualified Data.Set as Set
import Cardano.Ledger.Credential(Credential(..))
import Cardano.Ledger.Keys(KeyRole(..))
import Test.Cardano.Ledger.Generic.PrettyCore(PrettyA(..))
import Test.QuickCheck
import Cardano.Ledger.Coin
-}

vStateSpec :: Specification fn (VState (ConwayEra StandardCrypto))
vStateSpec = TrueSpec

govCertSpec ::
  IsConwayUniv fn =>
  ConwayGovCertEnv (ConwayEra StandardCrypto) ->
  VState (ConwayEra StandardCrypto) ->
  Specification fn (ConwayGovCert StandardCrypto)
govCertSpec ConwayGovCertEnv {..} vs =
  let reps = lit $ Map.keysSet $ vsDReps vs
      deposits = Map.map drepDeposit (vsDReps vs)
      getNewMembers = \case
        UpdateCommittee _ _ newMembers _ -> Map.keysSet newMembers
        _ -> mempty
      knownColdCreds =
        Map.keysSet (foldMap committeeMembers cgceCurrentCommittee)
          <> foldMap (getNewMembers . pProcGovAction . gasProposalProcedure) cgceCommitteeProposals
      ccCertSpec coldCred =
        assert . member_ coldCred $ lit knownColdCreds
   in constrained $ \ [var|gc|] ->
        caseOn
          gc
          -- ConwayRegDRep
          ( branchW 1 $ \ [var|key1|] [var|coin1|] _ ->
              [ not_ $ member_ key1 reps
              , coin1 ==. lit (cgcePParams ^. ppDRepDepositL)
              ]
          )
          -- ConwayUnRegDRep
          ( branchW 2 $ \ [var|cred|] [var|coin2|] ->
              -- if one is really unlucky, the ConwayGovCertEnv and VState inputs can cause every branch of the caseOn
              -- to be false. The easies way to prevent this is to choose 1 branch (this one ConwaUnRegDRep)
              -- and make sure it is always solveable. We do this by generating a random ConwaUnRegDRep when
              -- vsDReps is null. But since this is a conformance test, the fact that this random signal may fail,
              -- is OK, since in conformance we only need to get the same result as the Spec (which presumably will also fail).
              if Map.null deposits
                then TruePred
                else forAll (lit deposits) (\p -> match p (\cr cn -> whenTrue (cred ==. cr) (assert $ coin2 ==. cn)))
          )
          -- ConwayUpdateDRep
          ( branchW 1 $ \ [var|key2|] _ ->
              member_ key2 reps
          )
          -- ConwayAuthCommitteeHotKey
          (branchW 1 $ \ [var|coldCred1|] _ -> ccCertSpec coldCred1)
          -- ConwayResignCommitteeColdKey
          (branchW 1 $ \ [var|coldCred2|] _ -> ccCertSpec coldCred2)

govCertEnvSpec ::
  IsConwayUniv fn =>
  Specification fn (ConwayGovCertEnv (ConwayEra StandardCrypto))
govCertEnvSpec =
  constrained $ \gce ->
    match gce $ \pp _ _ _ ->
      satisfies pp pparamsSpec
