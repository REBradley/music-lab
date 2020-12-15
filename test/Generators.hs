module Generators where

import Euterpea
import Test.QuickCheck hiding (scale)

instance Arbitrary PitchClass where
  arbitrary = elements [Css .. Bss]
