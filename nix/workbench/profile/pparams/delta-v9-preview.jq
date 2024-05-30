## this delta does not include v8 preview changes
def delta:
{
  "shelley": {
    "protocolVersion": {
      "major": 9
    },
  },
  "costModels": {
    "PlutusV1": {
    },
    "PlutusV2": {
    },
    "PlutusV3": {
      "addInteger-cpu-arguments-intercept": 100788,
      "addInteger-cpu-arguments-slope": 420,
      "addInteger-memory-arguments-intercept": 1,
      "addInteger-memory-arguments-slope": 1,
      "appendByteString-cpu-arguments-intercept": 1000,
      "appendByteString-cpu-arguments-slope": 173,
      "appendByteString-memory-arguments-intercept": 0,
      "appendByteString-memory-arguments-slope": 1,
      "appendString-cpu-arguments-intercept": 1000,
      "appendString-cpu-arguments-slope": 59957,
      "appendString-memory-arguments-intercept": 4,
      "appendString-memory-arguments-slope": 1,
      "bData-cpu-arguments": 11183,
      "bData-memory-arguments": 32,
      "blake2b_224-cpu-arguments-intercept": 207616,
      "blake2b_224-cpu-arguments-slope": 8310,
      "blake2b_224-memory-arguments": 4,
      "blake2b_256-cpu-arguments-intercept": 201305,
      "blake2b_256-cpu-arguments-slope": 8356,
      "blake2b_256-memory-arguments": 4,
      "bls12_381_G1_add-cpu-arguments": 962335,
      "bls12_381_G1_add-memory-arguments": 18,
      "bls12_381_G1_compress-cpu-arguments": 2780678,
      "bls12_381_G1_compress-memory-arguments": 6,
      "bls12_381_G1_equal-cpu-arguments": 442008,
      "bls12_381_G1_equal-memory-arguments": 1,
      "bls12_381_G1_hashToGroup-cpu-arguments-intercept": 52538055,
      "bls12_381_G1_hashToGroup-cpu-arguments-slope": 3756,
      "bls12_381_G1_hashToGroup-memory-arguments": 18,
      "bls12_381_G1_neg-cpu-arguments": 267929,
      "bls12_381_G1_neg-memory-arguments": 18,
      "bls12_381_G1_scalarMul-cpu-arguments-intercept": 76433006,
      "bls12_381_G1_scalarMul-cpu-arguments-slope": 8868,
      "bls12_381_G1_scalarMul-memory-arguments": 18,
      "bls12_381_G1_uncompress-cpu-arguments": 52948122,
      "bls12_381_G1_uncompress-memory-arguments": 18,
      "bls12_381_G2_add-cpu-arguments": 1995836,
      "bls12_381_G2_add-memory-arguments": 36,
      "bls12_381_G2_compress-cpu-arguments": 3227919,
      "bls12_381_G2_compress-memory-arguments": 12,
      "bls12_381_G2_equal-cpu-arguments": 901022,
      "bls12_381_G2_equal-memory-arguments": 1,
      "bls12_381_G2_hashToGroup-cpu-arguments-intercept": 166917843,
      "bls12_381_G2_hashToGroup-cpu-arguments-slope": 4307,
      "bls12_381_G2_hashToGroup-memory-arguments": 36,
      "bls12_381_G2_neg-cpu-arguments": 284546,
      "bls12_381_G2_neg-memory-arguments": 36,
      "bls12_381_G2_scalarMul-cpu-arguments-intercept": 158221314,
      "bls12_381_G2_scalarMul-cpu-arguments-slope": 26549,
      "bls12_381_G2_scalarMul-memory-arguments": 36,
      "bls12_381_G2_uncompress-cpu-arguments": 74698472,
      "bls12_381_G2_uncompress-memory-arguments": 36,
      "bls12_381_finalVerify-cpu-arguments": 333849714,
      "bls12_381_finalVerify-memory-arguments": 1,
      "bls12_381_millerLoop-cpu-arguments": 254006273,
      "bls12_381_millerLoop-memory-arguments": 72,
      "bls12_381_mulMlResult-cpu-arguments": 2174038,
      "bls12_381_mulMlResult-memory-arguments": 72,
      "byteStringToInteger-cpu-arguments-c0": 1006041,
      "byteStringToInteger-cpu-arguments-c1": 43623,
      "byteStringToInteger-cpu-arguments-c2": 251,
      "byteStringToInteger-memory-arguments-intercept": 0,
      "byteStringToInteger-memory-arguments-slope": 1,
      "cekApplyCost-exBudgetCPU": 16000,
      "cekApplyCost-exBudgetMemory": 100,
      "cekBuiltinCost-exBudgetCPU": 16000,
      "cekBuiltinCost-exBudgetMemory": 100,
      "cekCaseCost-exBudgetCPU": 16000,
      "cekCaseCost-exBudgetMemory": 100,
      "cekConstCost-exBudgetCPU": 16000,
      "cekConstCost-exBudgetMemory": 100,
      "cekConstrCost-exBudgetCPU": 16000,
      "cekConstrCost-exBudgetMemory": 100,
      "cekDelayCost-exBudgetCPU": 16000,
      "cekDelayCost-exBudgetMemory": 100,
      "cekForceCost-exBudgetCPU": 16000,
      "cekForceCost-exBudgetMemory": 100,
      "cekLamCost-exBudgetCPU": 16000,
      "cekLamCost-exBudgetMemory": 100,
      "cekStartupCost-exBudgetCPU": 100,
      "cekStartupCost-exBudgetMemory": 100,
      "cekVarCost-exBudgetCPU": 16000,
      "cekVarCost-exBudgetMemory": 100,
      "chooseData-cpu-arguments": 94375,
      "chooseData-memory-arguments": 32,
      "chooseList-cpu-arguments": 132994,
      "chooseList-memory-arguments": 32,
      "chooseUnit-cpu-arguments": 61462,
      "chooseUnit-memory-arguments": 4,
      "consByteString-cpu-arguments-intercept": 72010,
      "consByteString-cpu-arguments-slope": 178,
      "consByteString-memory-arguments-intercept": 0,
      "consByteString-memory-arguments-slope": 1,
      "constrData-cpu-arguments": 22151,
      "constrData-memory-arguments": 32,
      "decodeUtf8-cpu-arguments-intercept": 91189,
      "decodeUtf8-cpu-arguments-slope": 769,
      "decodeUtf8-memory-arguments-intercept": 4,
      "decodeUtf8-memory-arguments-slope": 2,
      "divideInteger-cpu-arguments-constant": 85848,
      "divideInteger-cpu-arguments-model-arguments-intercept": 228465,
      "divideInteger-cpu-arguments-model-arguments-slope": 122,
      "divideInteger-memory-arguments-intercept": 0,
      "divideInteger-memory-arguments-minimum": 1,
      "divideInteger-memory-arguments-slope": 1,
      "encodeUtf8-cpu-arguments-intercept": 1000,
      "encodeUtf8-cpu-arguments-slope": 42921,
      "encodeUtf8-memory-arguments-intercept": 4,
      "encodeUtf8-memory-arguments-slope": 2,
      "equalsByteString-cpu-arguments-constant": 24548,
      "equalsByteString-cpu-arguments-intercept": 29498,
      "equalsByteString-cpu-arguments-slope": 38,
      "equalsByteString-memory-arguments": 1,
      "equalsData-cpu-arguments-intercept": 898148,
      "equalsData-cpu-arguments-slope": 27279,
      "equalsData-memory-arguments": 1,
      "equalsInteger-cpu-arguments-intercept": 51775,
      "equalsInteger-cpu-arguments-slope": 558,
      "equalsInteger-memory-arguments": 1,
      "equalsString-cpu-arguments-constant": 39184,
      "equalsString-cpu-arguments-intercept": 1000,
      "equalsString-cpu-arguments-slope": 60594,
      "equalsString-memory-arguments": 1,
      "fstPair-cpu-arguments": 141895,
      "fstPair-memory-arguments": 32,
      "headList-cpu-arguments": 83150,
      "headList-memory-arguments": 32,
      "iData-cpu-arguments": 15299,
      "iData-memory-arguments": 32,
      "ifThenElse-cpu-arguments": 76049,
      "ifThenElse-memory-arguments": 1,
      "indexByteString-cpu-arguments": 13169,
      "indexByteString-memory-arguments": 4,
      "integerToByteString-cpu-arguments-c0": 1293828,
      "integerToByteString-cpu-arguments-c1": 28716,
      "integerToByteString-cpu-arguments-c2": 63,
      "integerToByteString-memory-arguments-intercept": 0,
      "integerToByteString-memory-arguments-slope": 1,
      "keccak_256-cpu-arguments-intercept": 2261318,
      "keccak_256-cpu-arguments-slope": 64571,
      "keccak_256-memory-arguments": 4,
      "lengthOfByteString-cpu-arguments": 22100,
      "lengthOfByteString-memory-arguments": 10,
      "lessThanByteString-cpu-arguments-intercept": 28999,
      "lessThanByteString-cpu-arguments-slope": 74,
      "lessThanByteString-memory-arguments": 1,
      "lessThanEqualsByteString-cpu-arguments-intercept": 28999,
      "lessThanEqualsByteString-cpu-arguments-slope": 74,
      "lessThanEqualsByteString-memory-arguments": 1,
      "lessThanEqualsInteger-cpu-arguments-intercept": 43285,
      "lessThanEqualsInteger-cpu-arguments-slope": 552,
      "lessThanEqualsInteger-memory-arguments": 1,
      "lessThanInteger-cpu-arguments-intercept": 44749,
      "lessThanInteger-cpu-arguments-slope": 541,
      "lessThanInteger-memory-arguments": 1,
      "listData-cpu-arguments": 33852,
      "listData-memory-arguments": 32,
      "mapData-cpu-arguments": 68246,
      "mapData-memory-arguments": 32,
      "mkCons-cpu-arguments": 72362,
      "mkCons-memory-arguments": 32,
      "mkNilData-cpu-arguments": 7243,
      "mkNilData-memory-arguments": 32,
      "mkNilPairData-cpu-arguments": 7391,
      "mkNilPairData-memory-arguments": 32,
      "mkPairData-cpu-arguments": 11546,
      "mkPairData-memory-arguments": 32,
      "modInteger-cpu-arguments-constant": 85848,
      "modInteger-cpu-arguments-model-arguments-intercept": 228465,
      "modInteger-cpu-arguments-model-arguments-slope": 122,
      "modInteger-memory-arguments-intercept": 0,
      "modInteger-memory-arguments-minimum": 1,
      "modInteger-memory-arguments-slope": 1,
      "multiplyInteger-cpu-arguments-intercept": 90434,
      "multiplyInteger-cpu-arguments-slope": 519,
      "multiplyInteger-memory-arguments-intercept": 0,
      "multiplyInteger-memory-arguments-slope": 1,
      "nullList-cpu-arguments": 74433,
      "nullList-memory-arguments": 32,
      "quotientInteger-cpu-arguments-constant": 85848,
      "quotientInteger-cpu-arguments-model-arguments-intercept": 228465,
      "quotientInteger-cpu-arguments-model-arguments-slope": 122,
      "quotientInteger-memory-arguments-intercept": 0,
      "quotientInteger-memory-arguments-minimum": 1,
      "quotientInteger-memory-arguments-slope": 1,
      "remainderInteger-cpu-arguments-constant": 85848,
      "remainderInteger-cpu-arguments-model-arguments-intercept": 228465,
      "remainderInteger-cpu-arguments-model-arguments-slope": 122,
      "remainderInteger-memory-arguments-intercept": 0,
      "remainderInteger-memory-arguments-minimum": 1,
      "remainderInteger-memory-arguments-slope": 1,
      "serialiseData-cpu-arguments-intercept": 955506,
      "serialiseData-cpu-arguments-slope": 213312,
      "serialiseData-memory-arguments-intercept": 0,
      "serialiseData-memory-arguments-slope": 2,
      "sha2_256-cpu-arguments-intercept": 270652,
      "sha2_256-cpu-arguments-slope": 22588,
      "sha2_256-memory-arguments": 4,
      "sha3_256-cpu-arguments-intercept": 1457325,
      "sha3_256-cpu-arguments-slope": 64566,
      "sha3_256-memory-arguments": 4,
      "sliceByteString-cpu-arguments-intercept": 20467,
      "sliceByteString-cpu-arguments-slope": 1,
      "sliceByteString-memory-arguments-intercept": 4,
      "sliceByteString-memory-arguments-slope": 0,
      "sndPair-cpu-arguments": 141992,
      "sndPair-memory-arguments": 32,
      "subtractInteger-cpu-arguments-intercept": 100788,
      "subtractInteger-cpu-arguments-slope": 420,
      "subtractInteger-memory-arguments-intercept": 1,
      "subtractInteger-memory-arguments-slope": 1,
      "tailList-cpu-arguments": 81663,
      "tailList-memory-arguments": 32,
      "trace-cpu-arguments": 59498,
      "trace-memory-arguments": 32,
      "unBData-cpu-arguments": 20142,
      "unBData-memory-arguments": 32,
      "unConstrData-cpu-arguments": 24588,
      "unConstrData-memory-arguments": 32,
      "unIData-cpu-arguments": 20744,
      "unIData-memory-arguments": 32,
      "unListData-cpu-arguments": 25933,
      "unListData-memory-arguments": 32,
      "unMapData-cpu-arguments": 24623,
      "unMapData-memory-arguments": 32,
      "verifyEcdsaSecp256k1Signature-cpu-arguments": 43053543,
      "verifyEcdsaSecp256k1Signature-memory-arguments": 10,
      "verifyEd25519Signature-cpu-arguments-intercept": 53384111,
      "verifyEd25519Signature-cpu-arguments-slope": 14333,
      "verifyEd25519Signature-memory-arguments": 10,
      "verifySchnorrSecp256k1Signature-cpu-arguments-intercept": 43574283,
      "verifySchnorrSecp256k1Signature-cpu-arguments-slope": 26308,
      "verifySchnorrSecp256k1Signature-memory-arguments": 10
    }
  },
  "conway": {
    "plutusV3CostModel":
      [
        100788,
        420,
        1,
        1,
        1000,
        173,
        0,
        1,
        1000,
        59957,
        4,
        1,
        11183,
        32,
        201305,
        8356,
        4,
        16000,
        100,
        16000,
        100,
        16000,
        100,
        16000,
        100,
        16000,
        100,
        16000,
        100,
        100,
        100,
        16000,
        100,
        94375,
        32,
        132994,
        32,
        61462,
        4,
        72010,
        178,
        0,
        1,
        22151,
        32,
        91189,
        769,
        4,
        2,
        85848,
        228465,
        122,
        0,
        1,
        1,
        1000,
        42921,
        4,
        2,
        24548,
        29498,
        38,
        1,
        898148,
        27279,
        1,
        51775,
        558,
        1,
        39184,
        1000,
        60594,
        1,
        141895,
        32,
        83150,
        32,
        15299,
        32,
        76049,
        1,
        13169,
        4,
        22100,
        10,
        28999,
        74,
        1,
        28999,
        74,
        1,
        43285,
        552,
        1,
        44749,
        541,
        1,
        33852,
        32,
        68246,
        32,
        72362,
        32,
        7243,
        32,
        7391,
        32,
        11546,
        32,
        85848,
        228465,
        122,
        0,
        1,
        1,
        90434,
        519,
        0,
        1,
        74433,
        32,
        85848,
        228465,
        122,
        0,
        1,
        1,
        85848,
        228465,
        122,
        0,
        1,
        1,
        955506,
        213312,
        0,
        2,
        270652,
        22588,
        4,
        1457325,
        64566,
        4,
        20467,
        1,
        4,
        0,
        141992,
        32,
        100788,
        420,
        1,
        1,
        81663,
        32,
        59498,
        32,
        20142,
        32,
        24588,
        32,
        20744,
        32,
        25933,
        32,
        24623,
        32,
        43053543,
        10,
        53384111,
        14333,
        10,
        43574283,
        26308,
        10,
        16000,
        100,
        16000,
        100,
        962335,
        18,
        2780678,
        6,
        442008,
        1,
        52538055,
        3756,
        18,
        267929,
        18,
        76433006,
        8868,
        18,
        52948122,
        18,
        1995836,
        36,
        3227919,
        12,
        901022,
        1,
        166917843,
        4307,
        36,
        284546,
        36,
        158221314,
        26549,
        36,
        74698472,
        36,
        333849714,
        1,
        254006273,
        72,
        2174038,
        72,
        2261318,
        64571,
        4,
        207616,
        8310,
        4,
        1293828,
        28716,
        63,
        0,
        1,
        1006041,
        43623,
        251,
        0,
        1
      ]
  }
};
