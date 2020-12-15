module MusicPercussionSound where

import Euterpea hiding (perc)
import HSoM
import Control.DeepSeq

instance ToMusic1 PercussionSound where
  toMusic1 = mMap (\p -> (pitch $ fromEnum p + 35,[]))

instance NFData PercussionSound where
  rnf x = seq x () 

perc :: Dur -> PercussionSound -> Music PercussionSound
perc = note

class Sound a where
  toScore :: Dur -> a -> Music a

instance Sound PercussionSound where
  toScore = perc
