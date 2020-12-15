module Types 
  ( mkBar
  , getBar
) where

import Euterpea

data Bar a = UnsafeBarConstructor Dur (Music a)
  deriving Show

mkBar      :: Dur -> Music a -> Either String (Bar a)
mkBar bd m =
  if dur m == bd
    then Right (UnsafeBarConstructor bd m)
    else Left (show $ dur m)

getBar :: Either String (Bar a) -> Music a
getBar (Right (UnsafeBarConstructor _ m)) = m
getBar (Left _)                           = rest 0



data PercussionLine = 
  PercussionLine  { bDrum     :: PercussionSound
                  , snareDrum :: PercussionSound
                  , hatDrum   :: PercussionSound
                  }

bassLine :: PercussionSound -> Music a -> Music a
bassLine p = Modify $ Instrument (bDrum p)


