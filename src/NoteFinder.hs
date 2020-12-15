module NoteFinder (
  scale,
  scaleOctave,
  Degree,
  modeToIntervals,
  chordProgression, -- [[AbsPitch]]
  chordsToMusic,    -- Music Pitch
  noteToChord,
  mkKey,
  findDegree,
  majorScaleTriads,
  natMinorScaleTriads,
  triadType, 
  majorIntervals,
  natMinorIntervals,
  findKey,
  modulateUp,
  modulateDn,
  changeKey
  ) where

import Prelude
import Euterpea
import Data.List (zipWith)


findKey :: Music Pitch -> [((PitchClass,Mode),[PitchClass])]
findKey m = 
  let rmffss = \((pc,mo),ps) -> pc `notElem` ffss
  in filter rmffss $ foldl f allks (mPitch m)
  where allks = map (mkKey Major) [C ..] ++ map (mkKey Minor) [C ..]
        f ks p = filter (elem (fst . rmEnhEq $ p) . snd) ks
        rmEnhEq = pitch . absPitch

ffss = [Cff,Dff,Css,Eff,Fff,Dss,Gff,Ess,Fss,Aff,Gss,Bff,Ass,Bss]

mPitch :: Music a -> [a]
mPitch = mFold primPitch (++) (++) (\_ m -> m)

primPitch :: Primitive a -> [a]
primPitch (Note d x) = [x]
primPitch (Rest d)   = []

mkKey :: Mode -> PitchClass -> ((PitchClass, Mode),[PitchClass])
mkKey mo pc = ((pc,mo), map (fst . pitch) oct)
  where oct = take 7 $ scale ap mo
        ap  = absPitch (pc,1)

type Vector = [Int]
type Scale  = [AbsPitch]
type Degree = Int

majorIntervals, natMinorIntervals :: Vector
majorIntervals = cycle [2,2,1,2,2,2,1]
natMinorIntervals = cycle [2,1,2,2,1,2,2]
majorPentatonicIntervals = cycle [2,2,3,2,3]
minorPentatonicIntervals = cycle [3,2,2,3,2]

triadType :: [AbsPitch] -> String
triadType [p1,p2,p3] | p2 - p1 == 4 && p3 - p2 == 3 = "Major"
                     | p2 - p1 == 3 && p3 - p2 == 4 = "Minor"
                     | p2 - p1 == 3 && p3 - p2 == 3 = "Diminished"
                     | otherwise                    = "Augmented"
triadType _ = "Not a triad."

majorScaleTriads :: [String]
majorScaleTriads = 
  ["Major","Minor","Minor","Major","Major","Minor","Diminished"] 

natMinorScaleTriads :: [String]
natMinorScaleTriads = 
  ["Minor","Diminished","Major","Minor","Minor","Major","Major"]

scale :: AbsPitch -> Mode -> Scale
scale tonic mo = scanl (+) tonic (modeToIntervals mo)

modeToIntervals mo = 
  case mo of
    Minor        -> natMinorIntervals
    CustomMode s -> modeStrToIntervals s
    _            -> majorIntervals
  where modeStrToIntervals s
          | s == "MajorPentatonic" = majorPentatonicIntervals
          | s == "MinorPentatonic" = minorPentatonicIntervals

scaleOctave :: Mode -> Pitch -> Music Pitch
scaleOctave mo p = line $ take 7 $ s
  where s = map (note wn . pitch) $ scale (absPitch p) mo


------------
-- Chords --
------------

triad :: [AbsPitch] -> AbsPitch -> [AbsPitch]
triad key root = mkChord 3 key root

mkChord :: Int -> [AbsPitch] -> AbsPitch -> [AbsPitch]
mkChord size key rt = 
  take size bigChord
    where rootscalenotes           = scale rt Major
          tonicThrdFthEtc (x:_:xs) = x : tonicThrdFthEtc xs
          chordNotes               = tonicThrdFthEtc rootscalenotes
          bigChord                 = map (checkDim key) chordNotes

checkDim :: [AbsPitch] -> AbsPitch -> AbsPitch
checkDim key ap = 
  if ap `elem` (takeWhile (<= ap) key) 
    then ap 
    else ap - 1


chordProgression :: Pitch -> Mode -> [Degree] -> [[AbsPitch]]
chordProgression k mo ds = map (triad key) $ getRoots ds key
    where key = scale ap mo
          ap  = absPitch k

getRoots :: [Degree] -> Scale -> [AbsPitch]
getRoots [] _ = []
getRoots (d:ds) s = s !! (d-1) : getRoots ds s

--length ds `compare` length chs what's the right way?
chordsToMusic :: [Dur] -> [[AbsPitch]] -> Music Pitch
chordsToMusic ds chs = mMap pitch $ line $ map chord $ 
                       zipWith map (note <$> ds) chs

-- Note must be in key of k!
noteToChord :: Pitch -> Mode -> Music Pitch -> Music Pitch
noteToChord k mo (Prim (Note d p)) = 
  chordsToMusic [d] $ chordProgression k mo [deg] 
  where (deg,_)  = findDegree k mo p
noteToChord _ _ m                  = m

findDegree :: Pitch -> Mode -> (Pitch -> (Degree,AbsPitch))
findDegree k mo p = (length ps, last ps)
  where ap  = absPitch p
        key = absPitch k
        ps  = takeWhile (<= ap) (scale key mo)



---------------------------------------
-- Circle of Fifths & Key Modulation --
---------------------------------------

-- Some enharmonics missing
cof = cycle 
  [(C,A),(G,E),(D,B),(A,Fs),
   (E,Cs),(B,Gs),(Fs,Ds),(Cs,As),
   (Af,F),(Ef,C),(Bf,G),(F,D)]


changeKey :: Int -> (PitchClass,Mode) -> (PitchClass,Mode) -> (Pitch -> Pitch)
changeKey delta (opc,omo) (npc,nmo) p@(pc,o) = 
  let newpc = (snd $ mkKey nmo npc) !! ((fst $ findDegree (opc,o) omo p) - 1)
      nwoct = if newpc `elem` remOctave then o 
                                        else o + delta
  in (newpc,nwoct)
  where remOctave | delta >= 0 = [opc ..]
                  | delta <  0 = [opc,toEnum(fromEnum opc - 1) ..]

-- Assumption: All pitches are in Key oldk
modulateUp,modulateDn :: (PitchClass, Mode) -> (PitchClass, Mode) 
                          -> (Music Pitch -> Music Pitch)
modulateUp oldk newk = mMap (changeKey 1 oldk newk)
modulateDn oldk newk = mMap (changeKey (-1) oldk newk)

