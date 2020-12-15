module Testing where

import Test.QuickCheck
import Euterpea


prop_associativityMinMax :: NonNegative Rational -> NonNegative Rational -> Bool
prop_associativityMinMax x y = x `min` (y `max` z) == (x `min` y) `max` z
                             where z = NonNegative {getNonNegative = 0}

prop_assocMinOverRationals :: Rational -> Rational -> Rational -> Bool
prop_assocMinOverRationals x y z = x `min` (y `min` z) == (x `min` y) `min` z

prop_MinMax :: NonNegative Rational -> NonNegative Rational -> Bool
prop_MinMax x y = (x `max` z) `min` y == (x `min` y) `max` z
                             where z = NonNegative {getNonNegative = 0}

prop_subtractMinMax :: NonNegative Rational -> 
                       NonNegative Rational -> 
                       NonNegative Rational -> 
                       Property
prop_subtractMinMax x y d = 
  (x > d && y > d) ==> 
  (((f (x `min` y) - f d) `max` 0) ==  ((f (x `min` y) `max` 0) - f d))
  where f = getNonNegative



--min (max x 0) y = max (min x y) 0
--(x `max` 0) `min` y = (x `min` y) `max` 0
