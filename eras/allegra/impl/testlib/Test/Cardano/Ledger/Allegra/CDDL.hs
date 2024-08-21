{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Evaluate" #-}

module Test.Cardano.Ledger.Allegra.CDDL where

import Codec.CBOR.Cuddle.Huddle
import Data.Function (($))
import Test.Cardano.Ledger.Core.Binary.CDDL hiding (set)
import Test.Cardano.Ledger.Shelley.CDDL (
  bootstrap_witness,
  certificate,
  header,
  metadata_hash,
  set,
  transaction_index,
  transaction_input,
  transaction_metadatum,
  transaction_metadatum_label,
  transaction_output,
  update,
  vkeywitness,
  withdrawals,
 )

cddl :: Huddle
cddl = collectFrom [block, transaction]

--------------------------------------------------------------------------------
-- Things changed in Allegra
--------------------------------------------------------------------------------

native_script :: Rule
native_script =
  comment "Timelock validity intervals are half-open intervals [a, b)." $
    "native_script"
      =:= arr [a script_pubkey]
      / arr [a script_all]
      / arr [a script_any]
      / arr [a script_n_of_k]
      / arr [a invalid_before]
      -- Timelock validity intervals are half-open intervals [a, b).
      -- This field specifies the left (included) endpoint a.
      / arr [a invalid_hereafter]

-- Timelock validity intervals are half-open intervals [a, b).
-- This field specifies the right (excluded) endpoint b.

script_pubkey :: Named Group
script_pubkey = "script_pubkey" =:~ grp [0, a addr_keyhash]

script_all :: Named Group
script_all = "script_all" =:~ grp [1, a (arr [0 <+ a native_script])]

script_any :: Named Group
script_any = "script_any" =:~ grp [2, a (arr [0 <+ a native_script])]

script_n_of_k :: Named Group
script_n_of_k =
  "script_n_of_k"
    =:~ grp [3, "n" ==> int64, a (arr [0 <+ a native_script])]

invalid_before :: Named Group
invalid_before = "invalid_before" =:~ grp [4, a VUInt]

invalid_hereafter :: Named Group
invalid_hereafter = "invalid_hereafter" =:~ grp [5, a VUInt]

transaction_witness_set :: Rule
transaction_witness_set =
  "transaction_witness_set"
    =:= mp
      [ opt $ idx 0 ==> arr [0 <+ a vkeywitness]
      , opt $ idx 1 ==> arr [0 <+ a native_script]
      , opt $ idx 2 ==> arr [0 <+ a bootstrap_witness]
      ]

auxiliary_data :: Rule
auxiliary_data =
  "auxiliary_data"
    =:= smp
      [ 0
          <+ asKey transaction_metadatum_label
          ==> transaction_metadatum
      ]
    / sarr
      [ "transaction_metadata"
          ==> mp
            [ 0
                <+ asKey transaction_metadatum_label
                ==> transaction_metadatum
            ]
      , "auxiliary_scripts" ==> arr [0 <+ a native_script]
      ]

transaction_body :: Rule
transaction_body =
  comment
    "Allegra transaction body adds the validity interval start at index 8"
    $ "transaction_body"
      =:= mp
        [ idx 0 ==> set transaction_input
        , idx 1 ==> arr [0 <+ a transaction_output]
        , idx 2 ==> coin
        , idx 3 ==> VUInt
        , opt (idx 4 ==> arr [0 <+ a certificate])
        , opt (idx 5 ==> withdrawals)
        , opt (idx 6 ==> update)
        , opt (idx 7 ==> metadata_hash)
        , opt (idx 8 ==> VUInt)
        ]

--------------------------------------------------------------------------------
-- Closure
--------------------------------------------------------------------------------

block :: Rule
block =
  "block"
    =:= arr
      [ a header
      , "transaction_bodies" ==> arr [0 <+ a transaction_body]
      , "transaction_witness_sets"
          ==> arr [0 <+ a transaction_witness_set]
      , "auxiliary_data_set"
          ==> mp [0 <+ asKey transaction_index ==> auxiliary_data]
      ]

transaction :: Rule
transaction =
  "transaction"
    =:= arr
      [ a transaction_body
      , a transaction_witness_set
      , a (auxiliary_data / VNil)
      ]
