{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Cardano.Ledger.Api.State.Query (
  -- * @GetFilteredDelegationsAndRewardAccounts@
  filterStakePoolDelegsAndRewards,
  queryStakePoolDelegsAndRewards,

  -- * @GetGovState@
  queryGovState,

  -- * @GetConstitution@
  queryConstitution,

  -- * @GetConstitutionHash@
  queryConstitutionHash,

  -- * @GetDRepState@
  queryDRepState,

  -- * @GetDRepStakeDistr@
  queryDRepStakeDistr,

  -- * @GetCommitteeState@
  queryCommitteeState,
  -- HotCredAuthStaus(..),
) where

import Cardano.Ledger.Allegra.Core (Constitution (constitutionAnchor))
import Cardano.Ledger.BaseTypes (EpochNo)
import Cardano.Ledger.CertState
import Cardano.Ledger.Coin (Coin)
import Cardano.Ledger.Compactible (fromCompact)
import Cardano.Ledger.Core
import Cardano.Ledger.Credential (Credential)
import Cardano.Ledger.DRepDistr (drepExpiryL)
import Cardano.Ledger.Keys (KeyHash, KeyRole (..))
import Cardano.Ledger.SafeHash (SafeHash)
import Cardano.Ledger.Shelley.Governance (EraGov (GovState, getConstitution, getDRepDistr))
import Cardano.Ledger.Shelley.LedgerState
import Cardano.Ledger.UMap (
  StakeCredentials (scRewards, scSPools),
  UMap,
  domRestrictedStakeCredentials,
 )
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import Lens.Micro

-- | Filter out stake pool delegations and rewards for a set of stake credentials
filterStakePoolDelegsAndRewards ::
  UMap c ->
  Set (Credential 'Staking c) ->
  (Map (Credential 'Staking c) (KeyHash 'StakePool c), Map (Credential 'Staking c) Coin)
filterStakePoolDelegsAndRewards umap creds =
  (scSPools stakeCredentials, scRewards stakeCredentials)
  where
    stakeCredentials = domRestrictedStakeCredentials creds umap

-- | Uses `filterStakePoolDelegsAndRewards` to get the same information from the `NewEpochState`
--
-- Implementation for @GetFilteredDelegationsAndRewardAccounts@ query.
queryStakePoolDelegsAndRewards ::
  NewEpochState era ->
  Set (Credential 'Staking (EraCrypto era)) ->
  ( Map (Credential 'Staking (EraCrypto era)) (KeyHash 'StakePool (EraCrypto era))
  , Map (Credential 'Staking (EraCrypto era)) Coin
  )
queryStakePoolDelegsAndRewards nes = filterStakePoolDelegsAndRewards (dsUnified (getDState nes))

getDState :: NewEpochState era -> DState era
getDState = certDState . lsCertState . esLState . nesEs

queryConstitution :: EraGov era => NewEpochState era -> Maybe (Constitution era)
queryConstitution = getConstitution . queryGovState

queryConstitutionHash ::
  EraGov era =>
  NewEpochState era ->
  Maybe (SafeHash (EraCrypto era) AnchorData)
queryConstitutionHash nes =
  anchorDataHash . constitutionAnchor <$> queryConstitution nes

-- | This query returns all of the state related to governance
queryGovState :: NewEpochState era -> GovState era
queryGovState nes = nes ^. nesEpochStateL . esLStateL . lsUTxOStateL . utxosGovStateL

-- | Query DRep state.
queryDRepState ::
  NewEpochState era ->
  -- | Specify a set of DRep credentials whose state should be returned. When this set is
  -- empty, states for all of the DReps will be returned.
  Set (Credential 'DRepRole (EraCrypto era)) ->
  Map (Credential 'DRepRole (EraCrypto era)) (DRepState (EraCrypto era))
queryDRepState nes creds
  | null creds = drepsState
  | otherwise =
      drepsState `Map.restrictKeys` creds
        & if numDormantEpochs == 0
          then id
          else (<&> drepExpiryL %~ (+ numDormantEpochs))
  where
    drepsState = vsDReps $ certVState $ lsCertState $ esLState $ nesEs nes
    numDormantEpochs = vsNumDormantEpochs $ certVState $ lsCertState $ esLState $ nesEs nes

-- | Query DRep stake distribution. Note that this can be an expensive query because there
-- is a chance that current distribution has not been fully computed yet.
queryDRepStakeDistr ::
  EraGov era =>
  NewEpochState era ->
  -- | Specify DRep Ids whose stake distribution should be returned. When this set is
  -- empty, distributions for all of the DReps will be returned.
  Set (DRep (EraCrypto era)) ->
  Map (DRep (EraCrypto era)) Coin
queryDRepStakeDistr nes creds
  | null creds = Map.map fromCompact distr
  | otherwise = Map.map fromCompact $ distr `Map.restrictKeys` creds
  where
    distr = getDRepDistr (nes ^. newEpochStateGovStateL)

-- | Query committee members
queryCommitteeState :: NewEpochState era -> CommitteeState era
queryCommitteeState nes = undefined

-- vsCommitteeState $ certVState $ lsCertState $ esLState $ nesEs nes

-- -- | Query committee members
-- queryCommitteeMembers ::
--   Set (Credential 'ColdCommiteeRole c) ->
--   -- ^ filter by cold credentials (don't filter, when empty)
--   Set (Credential 'HotCommitteeRole c) ->
--   -- ^ filter by hot credentials (don't filter, when empty)
--   Maybe MemberStatus ->
--   -- ^ filter by status (don't filter, when Nothing)
--   -- (useful, for discovering, for exmple, only active members)
--   NewEpochState era ->
--   CommitteeMembersState era

-- data CommitteeMembersState c = CommitteeMembersState
-- {
--   cmsHotCredAuthStatus :: HotCredAuthStatus
-- }
