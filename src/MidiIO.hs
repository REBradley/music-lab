module MidiIO where

import Euterpea
import HSoM

-------------
-- Players --
-------------



-------------
-- To Midi --
-------------

writeMusicSequence :: [FilePath] -> [Music1] -> IO ()
writeMusicSequence n m = sequence_ $ map writeToPath (zip n m)

writeToPath :: (FilePath, Music1) -> IO ()
writeToPath (pth,m) = writeMidiA pth defPMap defCon $ m

nameList :: Int -> FilePath -> [FilePath]
nameList n fp = map (\i -> fp ++ show i ++ "algogen.mid") [1..n]
