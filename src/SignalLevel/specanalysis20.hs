{-# LANGUAGE Arrows, ExistentialQuantification, ScopedTypeVariables #-}

module SignalLevel.SpecAnalysis20 where

import Data.Complex
import Data.Maybe (catMaybes,listToMaybe)
import qualified Data.Map as M
import Control.Arrow.ArrowP
import Control.DeepSeq (NFData)
import Control.SF.SF (SF(..))
import FRP.UISF (SEvent,asyncVT,Time,DeltaT)
import FRP.UISF.Asynchrony (Automaton(..))
import FRP.UISF.Graphics.Color (rgbE)

import Euterpea hiding (SF)
import HSoM
import HSoM.MUI (asyncV)
import HSoM.Examples.FFT (fftA,quantize,presentFFT)

import SignalLevel.SigFun19

dft :: RealFloat a => [Complex a] -> [Complex a]
dft xs =
  let lenI = length xs
      lenR = fromIntegral lenI
      lenC = lenR :+ 0
  in [let i = -2*pi * fromIntegral k / lenR
      in (1/lenC) * sum [(xs !! n) * exp (0 :+ i * fromIntegral n)
                          | n <- [0,1..lenI-1]]
       | k <- [0,1..lenI-1]]


-- num = # samples
-- n   = term

mkTerm :: Int -> Double -> [Complex Double]
mkTerm num n = let f = 2*pi / fromIntegral num
  in [sin (n*f*fromIntegral i) / n :+ 0
       | i <- [0,1..num-1]]

mkxa,mkxb,mkxc :: Int -> [Complex Double]
mkxa num = mkTerm num 1
mkxb num = zipWith (+) (mkxa num) (mkTerm num 3)
mkxc num = zipWith (+) (mkxb num) (mkTerm num 5)

mkPulse :: Int -> [Complex Double]
mkPulse n = 100 : take (n-1) (repeat 0)

x1 num = let f = 2*pi*pi / fromIntegral num
  in map (:+ 0) [sin (f * fromIntegral i)
                  | i <- [0,1..num-1]]

mkPolars :: [Complex Double] -> [Complex Double]
mkPolars = map ((\(m,p) -> m :+ p) . polar)

---------------
-- Exercises --
---------------

{- Exercise 20.1©:Write a Haskell function idft that implements the inverse DFT
 - as captured in Equation 20.3. Test your code by applying idft to one of the
 - signals used earlier in this section. In other words, show empirically that,
 - up to round-off errors, idft (dft xs) == xs. -}

idft :: RealFloat a => [Complex a] -> [Complex a]
idft xs = let lenI = length xs 
              lenR = fromIntegral lenI
          in [let i = 2*pi* fromIntegral n / lenR
              in sum [(xs !! k) * exp (0 :+ i * fromIntegral k) 
                     | k <- [0..lenI-1]]
             | n <- [0..lenI-1]]


{- Exercise 20.2: Use dft to analyze some of the signals generated using signal
 - functions defined in Chapter 19. -}

fft1 :: forall p . Clock p => SigFun p () (SEvent (M.Map Double Double))
fft1 = s1 >>> (fftA 128 256) >>> arr (fmap $ presentFFT $ rate (undefined :: p))


{- Exercise 20.3:© Define a function mkSqWave :: Int -> Int -> [Complex Double] 
 - such that mkSqWave num n is the sum of the first n terms of the Fourier
 - Series of a square wave, having num samples in the result. -}

mkSqWave :: Int -> Int -> [Complex Double]
mkSqWave num n = 
  foldr (zipWith (+) . (\i -> mkTerm i)) 
        (replicate num 0) 
        (filter odd [1..(2*n-1)])
  where mkTerm x = let f = 2 * pi / fromIntegral num
                       t = fromIntegral x
                   in [sin (t*f*fromIntegral i)/t:+0
                      | i <- [0,1..num-1]]



{- Exercise 20.4: -} 

{- a. © Prove mathematically that x and x^ are inverses. 

  Let X^ and X be the NxN matrices defined by

  X^(k,n) = (1/N) * w^(kn)
  X(n,k)    = (1/N) * w^(-(kn))

  where w = e^(-j2π/N)
  and (a,b) corresponds to the entry in the ath row and bth column of the matrix

  Prove X^ and X are inverses
  Proof:
    
    It suffices to prove (X^)X = I

    Thus I show 
      if p=q then X^X(p,q) = 1
      otherwise   X^X(p,q) = 0

    X^X(p,q) = X^(p,*)·X(*,q) = (1/N) ∑w^(pn)*w^(-(n*q))

    where X^(p,*) is the pth row of X^ , X(*,q) is the qth column of X and
    ∑ is a sum from 0 to N-1

    if p = q then
      X^X(p,q) = (1/N) ∑ w^(pn)/w^(nq) = (1/N) ∑ 1 =  (1/N)*N = 1

    if p ≠ q then
      X^X(p,q) = (1/N) ∑ w^(n(p-q)) 
               = (1 - (e^(-j*2π(p-q)/N))^N)/(1 - e^(-j*2π(p-q)/N))
               = (1 - (e^(-j*2π(p-q)))/(1 - e^(-j*2π(p-q)/N))
               = (1 - 1/(cos(2π(p-q)) + jsin(2π(p-q))))/(1 - e^(-j*2π(p-q)/N))
               = (1 - 1)/(1 - e^(-j*2π(p-q)/N))
               = 0

    Thus X^X = I, proving X^ and X are inverses.
-}























{- 
e1 = 
  \i -> (1/lenC)*sum[(cxs !! n)*exp(0 :+ i*fromIntegral n) | n <- [0,1..lenI-1]]

f = \exp -> let lenI = length cxs
            in let lenR = fromIntegral lenI
               in let lenC = lenR :+ 0
                  in exp

-> fdft = (f (concatMap 
               (\k -> let i = -2*pi*fromIntegral k/lenR in e1 i) 
               [0,1..lenI-1]
             )
          )

fix exp = \x -> let x = exp x in x
-}



{- b. Also prove, using equational reasoning, that dft and idft are 
 - inverses. (..., you may assume that Haskell numeric types 
 - obey the standard axioms of real arithmetic.)

idft(dft(cxs))  = cxs

idft(dft(cxs)) 
-> idft (let lenI = length cxs
             lenR = fromIntegral lenI
             lenC = lenR :+ 0
         in [let i = -2*pi*fromIntegral k/lenR
             in (1/lenC)*sum[(cxs !! n)*exp (0 :+ i*fromIntegral n)
                             | n <-  [0,1..lenI-1]]
              |k <- [0,1..lenI-1]] )

-> idft (let lenI = length cxs
             lenR = fromIntegral lenI
             lenC = lenR :+ 0
         in [let i = -2*pi*fromIntegral k/lenR
             in e1 i | k <- [0,1..lenI-1]] )

  -> concatMap 
       (\k -> let i = -2*pi*fromIntegral k/lenR in e1 i) 
       [0,1..lenI-1]

-> idft (f (concatMap 
             (\k -> let i = -2*pi*fromIntegral k/lenR in e1 i) 
             [0,1..lenI-1]
           )
        )

-> let lenI2 = length fdft
       lenR2 = fromIntegral lenI2
   in [let i2 = 2*pi* fromIntegral n2 / lenR2
       in sum [(fdft !! k) * exp (0 :+ i2 * fromIntegral k) | k <- [0..lenI2-1]]
        | n2 <- [0..lenI2-1]]

-> let lenI2 = length fdft
       lenR2 = fromIntegral lenI2
   in [let i2 = 2*pi* fromIntegral n2 / lenR2
       in sum [(fdft !! k) * exp (0 :+ i2 * fromIntegral k) | k <- [0..lenI2-1]]
        | n2 <- [0..lenI2-1]]
-}































fftEx :: UISF () ()
fftEx = 
  proc _ -> do
    f <- withDisplay $ hSlider (1,2000) 440 -< ()
    d <- clockedSFToUISF (0.1) fftDataSig -< f
    let (ds,ts) = unzip d
    _ <- histogram (makeLayout (Fixed {fixedSize = 500})
                               (Fixed {fixedSize = 150})) 
                                -< listToMaybe (catMaybes (snd $ unzip ds))
    _ <- realtimeGraph (makeLayout (Fixed {fixedSize = 500}) 
                                   (Fixed {fixedSize = 150})) 
                                   1 Black -< (zip (fst $ unzip ds) ts)
    m  <- withDisplay $ hSlider (1,2000) 20 -< ()
    d1 <- clockedSFToUISF (0.1) fftDataSig -< m
    let (ds1,ts1) = unzip d1
    _  <- histogram (makeLayout (Fixed {fixedSize = 500})
                               (Fixed {fixedSize = 150})) 
                                -< listToMaybe (catMaybes (snd $ unzip ds1))
    _ <- realtimeGraph (makeLayout (Fixed {fixedSize = 500}) 
                                   (Fixed {fixedSize = 150})) 
                                   1 Black -< (zip (fst $ unzip ds1) ts1)
    d3 <- clockedSFToUISF (0.1) fftDataSig -< (f+m)
    let (ds3,ts3) = unzip d3
    _  <- histogram (makeLayout (Fixed {fixedSize = 500})
                               (Fixed {fixedSize = 150})) 
                                -< listToMaybe (catMaybes (snd $ unzip ds3))
    outA -< ()
    where
      fftDataSig :: SigFun CtrRate Double (Double, SEvent [Double])
      fftDataSig = proc f -> do
        s <- osc (tableSinesN 4096 [1]) 0 -< f
        fftData <- fftA 128 256 -< s
        outA -< (s,fftData)

t0 = runMUI (defaultMUIParams
               {uiSize       = (500,900),
                uiBackground = rgbE 93 10 13,
                uiTitle      = "FFT Test"}) 
            fftEx

clockedSFToUISF :: forall a b c . (NFData b,Clock c) => 
                   DeltaT -> SigFun c a b -> UISF a [(b,Time)]
clockedSFToUISF buffer ~(ArrowP sf) = let r = rate (undefined :: c)
  in asyncV r buffer (toAutomaton sf)

toAutomaton :: forall a b . SF a b -> Automaton (->) a b
toAutomaton ~(SF f) = Automaton $ \a -> let (b,sf) = f a in (b,toAutomaton sf)


{- Exercise 20.5: Modify the program in 20.5 (fftEx) in the following ways:
 -
 - 1. Add a second slider, and use it to control the frequency of a second
 - oscillator.©
 - 2. Let s1 and s2 be the names of the signals whose frequencies are controlled
 - by the first and second sliders, respectively. Instead of displaying the FFT
 - of just s1, try a variety of combinations of s1 and s2, such as 
 - s1 + s2
 - s1 - s2
 - s1 * s2
 - 1/s1 + 1/s2
 - s1/s2
 - Comment on the results.
 - 3. Use s2 to control the frequency of s1 (as was done with vibrato in Ch.19).
 - Plot the fft of s1 and comment on the result.
 - 4. Instead of using osc to generate a pure sine wave, try using other
 - oscillators and/or table generators to create more complex tones, and plot
 - their FFTs. Comment on the results. -}









----------
-- Util --
----------
printComplexL :: [Complex Double] -> IO ()
printComplexL xs = 
  let f (i, rl :+ im) =
        do putStr (spaces (3 - length (show i)))
           putStr (show i ++ ":    ("          )
           putStr (niceNum rl ++ ", "         )
           putStr (niceNum im ++ ") \n"        )
   in mapM_ f (zip [0..length xs - 1] xs)

niceNum :: Double -> String
niceNum d =
  let d' = fromIntegral (round (1e10*d))/1e10
      (dec,fra) = break (== '.') (show d')
      (fra',exp) = break (== 'e') fra
  in spaces (3 - length dec) ++ dec ++ take 11 fra'
     ++ exp ++ spaces (12 - length fra' - length exp)

spaces :: Int -> String
spaces n = take n (repeat ' ')

