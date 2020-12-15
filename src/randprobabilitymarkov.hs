module RandProbabilityMarkov where

import Euterpea hiding (perc)
import MusicPercussionSound

import HSoM
import System.Random
import System.Random.Distributions
import qualified Data.MarkovChain as M
import Data.List


import Rhythm (randomLine)
import NoteFinder
import Drummers
import Rhythm
import Tonality
import qualified RhythmSpecs as RSpecs


sGen :: StdGen
sGen = mkStdGen 42

toAbsP1   :: Float -> AbsPitch
toAbsP1 x = round (40 * x + 30)

toAbsShift      :: Float -> (Float -> AbsPitch)
toAbsShift units = round . (+ units)

mkNote1 :: AbsPitch -> Music Pitch
mkNote1 = note tn . pitch

mkLine1 :: [AbsPitch] -> Music Pitch
mkLine1 rands = line $ take 32 $ map mkNote1 rands

-- uniform distribution
m1 :: Music Pitch
m1 = mkLine1 $ randomRs (30,70) sGen

-- linear distribution
m2 :: Music Pitch
m2 = let rs1 = rands linear sGen
     in mkLine1 (map toAbsP1 rs1)

-- exponential distribution
-- toAbsP1 is not appropriate; see m3 shift
m3     :: Float -> Music Pitch
m3 spread = let rs1 = rands (exponential spread) sGen
            in mkLine1 (map toAbsP1 rs1)

m3shft     :: Float -> Music Pitch
m3shft spread = let rs1 = rands (exponential spread) sGen
                in mkLine1 (map (toAbsShift 30)rs1)

-- gaussian distribution
m4        :: Float -> Float -> Music Pitch
m4 dev mean = let rs1 = rands (gaussian dev mean) sGen
              in mkLine1 (map toAbsP1 rs1)

{- Exercise 14.1: © 
 - Try playing each of the above melodies, and listen to the
 - musical differences. For lam, try values of 0.1, 1, 5, and 10. For mu, a
 - value of 0.5 will put the melody in the central part of the scale range. Then
 - try values of 0.01, 0.05, and 0.1 for sig.
 - :: IO ()
m1 :: Music Pitch -- uniform distribution
m2 :: Music Pitch -- linear distribution
m3 :: Float -> Music Pitch -- exponential distribution
m4 :: Float -> Float -> Music Pitch -- gaussian distribution
 -}

{- Exercise 14.2: 
 - Do the following (to create a melody)...
 -
 - © Try using some of the other probability distributions
 -   (e.g. ©Bilateral Exp, ©Cauchy, ©Poisson) to generate a melody
 -
 - © Instead of using a chromatic scale, use a diatonic or pentatonic scale
 -   mDiatonic, mPenta :: (Degree -> StdGen -> [Degree]) -> Music Pitch
 -
 - © Try using randomness to control parameters other than pitch; 
 -   in particular, duration and/or volume
 -   randDurLn :: StdGen -> Dur -> (Dur -> a -> Music a) -> [a] -> [Music a]
 -   randVolMel :: StdGen -> [Music Pitch] -> [Music (Pitch,Volume)]
 -   humanVol :: Volume -> IO Volume
-}

mBilExp :: Float -> Float -> Music Pitch
mBilExp mean spread = let rs1 = rands (bilExp spread) sGen :: [Float]
                      in mkLine1 $ map (toAbsShift mean) rs1

mCauchy :: Float -> Float -> Music Pitch
mCauchy mean density = let rs1 = rands (cauchy density) sGen :: [Float]
                       in mkLine1 $ map (toAbsShift mean) rs1

mPoisson :: Float -> Music Pitch
mPoisson mean = let raps = rands (poisson mean) sGen :: [AbsPitch]
                in mkLine1 raps

cMajSpec = ToneSpec
  { root = (Ef,4),
    mode = Major,
    maxd = 14,
    inst = HammondOrgan }

dPentaSpec = ToneSpec
  { root = (D,4),
    mode = CustomMode "MajorPentatonic",
    maxd = 10,
    inst = RhodesPiano }

mDiatonic, mPenta :: (Degree -> StdGen -> [Degree]) -> Music Pitch
mDiatonic rdg   = mkLine1 $ randTonalAPs cMajSpec rdg sGen
mPenta rdg = mkLine1 $ randTonalAPs dPentaSpec rdg sGen

randTonalAPs :: ToneSpec -> (Degree -> StdGen -> [Degree]) 
                -> StdGen -> [AbsPitch]
randTonalAPs ts rdg g = 
  let rt       = absPitch (root ts)
      mo       = mode ts
      toAp     = (mkDegToApMap rt mo)
      maxDeg   = maxd ts
      rDegrees = rdg maxDeg g
  in map toAp rDegrees

mkDegToApMap :: AbsPitch -> Mode -> (Degree -> AbsPitch)
mkDegToApMap root mo deg = root + sum (take (deg-1) intervals)
  where intervals = modeToIntervals mo

randDegUniform :: Degree -> StdGen -> [Degree]
randDegUniform max = randomRs (1,max)

randDegLinear :: Degree -> StdGen -> [Degree]
randDegLinear max g = let rs = (rands linear g :: [Float])
                      in map (round . (* fromIntegral max)) rs

-- Durs --

randDurLn :: StdGen -> Dur -> (Dur -> a -> Music a) -> [a] -> [Music a]
randDurLn g d sf ps = zipWith sf ds ps
  where ds     = cutAt d randds
        randds = map (allds !!) $ randomRs (0, length allds - 1) g

cutAt :: Dur -> ([Dur] -> [Dur])
cutAt d ds = last $ takeWhile ((<= d) . sum) (inits ds)
       
durs,ddurs,dddurs, allds :: [Dur]
durs   = [wn,hn,qn,en,sn,tn,sfn]
ddurs  = [dwn,dhn,dqn,den,dsn,dtn]
dddurs = [ddhn,ddqn,dden]
allds  = durs ++ ddurs ++ dddurs
       

-- Volume --
humanVol :: Volume -> IO Volume
humanVol v = do h <- randomRIO (-5,5) :: IO Int
                return (v + h)

randVolMel :: StdGen -> [Music Pitch] -> [Music (Pitch,Volume)]
randVolMel g ml = zipMarkings (randMarkings g) ml
  where zipMarkings = zipWith volMap

randMarkings :: StdGen -> [StdLoudness]
randMarkings g = randomlySelect markings
  where markings       = [PPP ..]
        randomlySelect = \vs -> map (vs !!) (randomRs (0,length vs - 1) g)

volMap :: StdLoudness -> (Music Pitch -> Music (Pitch,Volume))
volMap l = case l of
             PPP -> addVolume 40;  PP -> addVolume 50;  P   -> addVolume 60
             MP  -> addVolume 70;  SF -> addVolume 80;  MF  -> addVolume 90
             NF  -> addVolume 100; FF -> addVolume 110; FFF -> addVolume 120


------------------
-- Random Walks --
------------------
-- Gaussian distribution with mean set to 0
m5 :: Float -> Music Pitch
m5 sig = let rs1 = rands (gaussian sig 0) sGen
         in mkLine2 50 (map toAbsP2 rs1)

m5' g sig = let rs1 = rands (gaussian sig 0) g
            in mkLine2 50 (map toAbsP2 rs1)

-- exponential distribution with mean adjusted to 0
m6 :: Float -> Music Pitch
m6 lam = let rs1 = rands (exponential lam) sGen
         in mkLine2 50 (map (toAbsP2 . subtract (1/lam)) rs1)

m6' g lam = let rs1 = rands (exponential lam) g
            in mkLine2 50 (map (toAbsP2 . subtract (1/lam)) rs1)

mkLine2 :: AbsPitch -> [AbsPitch] -> Music Pitch
mkLine2 start rands =
  line (take 64 (map mkNote1 (scanl (+) start rands)))

toAbsP2 :: Float -> AbsPitch
toAbsP2 x = round (5 * x)


-------------------
-- Markov Chains --
-------------------

-- some sample training sequences
ps0,ps1,ps2 :: [Pitch]
ps0 = [(C,4),(D,4),(E,4)]
ps1 = [(C,4),(D,4),(E,4),(F,4),(G,4),(A,4),(B,4)]
ps2 = [(C,4),(E,4),(G,4),(E,4),(F,4),(A,4),(G,4),(E,4),
       (C,4),(E,4),(G,4),(E,4),(F,4),(D,4),(C,4)]

-- functions to package up run and runMulti
mc  ps  n = mkLine3 (M.run n ps 0 sGen)
mcm pss n = (mkLine3 . concat) (M.runMulti n pss 0 sGen)

-- music-making functions
mkLine3 :: [Pitch] -> Music Pitch
mkLine3 ps = line $ take 64 $ map mkNote3 ps

mkNote3 :: Pitch -> Music Pitch
mkNote3 = note tn

{- Exercise 14.2 © : Play with Markov chains. Use them to generate more
 - melodies, or to control other aspects of music, such as rhythm. Also
 - consider other kinds of training data rather than simply sequences of
 - pitches. -}

mcChordProgression :: Pitch -> Mode -> [Dur] -> StdGen -> Music Pitch
mcChordProgression k mo ds g = 
  chordsToMusic ds (chordProgression k mo (markovDegrees g))

markovDegrees :: StdGen ->[Degree]
markovDegrees g = M.run 1 trainDegrees 0 g
  where trainDegrees = [1,4,5,1,6,4,5,2,5,1] :: [Degree]



randMusicList :: Int -> (StdGen -> Music a) -> [Music a]
randMusicList n mGen = map (mGen . mkStdGen) [1..n]
