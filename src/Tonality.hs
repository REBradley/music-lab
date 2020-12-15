module Tonality where

import Euterpea
import NoteFinder (Degree)

data ToneSpec = ToneSpec
  { root :: Pitch,
    mode :: Mode,
    maxd :: Degree,
    inst :: InstrumentName }
