module SignalLevel.SoundAndSignals18 where

{- Exercise 18.1: For each of the follwing, say whether it is a longitudinal
 - wave or a transverse wave. -}

-- A vibrating violin string (transverse)
-- Stop and go trafic on a highway (longitudinal)
-- The "wave" in a crowd at a stadium (transverse)
-- "Water Hammer" in the plumbing of your house (longitudinal)
-- A water ripple caused by a stone falling in a pond (longitudinal)
-- A radio wave (transverse)



{- Exercise 18.2: You see a lightning strike, and five seconds later you hear 
 - the thunder. How far away is the lightning? -}

-- 343m/s * 5s = 1,715 meters



{- Exercise 18.3: You clap your hands in a canyon and two seconds later you hear
 - an echo. How far away is the (closest) canyon wall? -}

-- 2d = 2 * 343
--  d = 343 meters



{- Exercise 18.4: By what factor must one increasethe RMS level of a signal to
 - yield a 10dB increase in sound level? -}

-- 10log10(x*b/r) - 10log10(x/r) = 10dB
-- log10(b) = 1
-- b = 10 factor increase



{- Exercise 18.5: A dog can hear in the range 60-45,000Hz and a bat
 - 2,000-110,000 Hz. In terms of the frequency response, what are the
 - corresponding dynamic ranges for these two animals, and how do they compare
 - to that of humans? -}

-- Dog: 10log10(45,000/60) = 28.8dB
--
-- Bat: 10log10(110,000/2,000) = 17.4 dB
--
-- Human: 30 dB
--
-- Dogs and bats have a smaller dynamic range in frequency response than humans.
-- Surprisingly, bats have a much lower range, mostly becuase they can't hear
-- low frequencies well.



{- Exercise 18.6: What is the maximum number of audible overtones in a note
 - whose fundamental frequency is 100Hz? 500Hz? 1500Hz? 5kHz? -}

-- 100Hz     n*100 = 20,000
--               n = 200
--
-- 500Hz     n*500 = 20,000
--               n = 40
--
-- 1500Hz   n*1500 = 20,000
--               n = 13.3 ≈ 13
--
-- 5000Hz   n*5000 = 20,000
--               n = 4



{- Exercise 18.7: Consider a continuous input signal whose frequency is f.
 - Devise a formula for the frequency r of the reproduced signal given a sample
 - rate s. -}

-- Let r = reproduced signal frequency
--     f = input frequency
--     s = sample rate
--
r :: Double -> Double
r f = abs $ f - s * (fromIntegral . round) (f / s)
  where s = 100


{- Exercise 18.8: How much memory is needed to record three minutes of stereo
 - sound using 16-bit samples taken at a rate of 44.1kHz? -}

-- 180 * 44,100 * 16 * 2 = 254,016,000 bits
--                       = 31,752,000 bytes
--                       = 31,752 Kb
--                       = 31.752 Mb



{- Exercise 18.9: If we want the best possible sound, how large should the tble
 - be using fixed-waveform table-lookup synthesis in order to cover the audible
 - frequency range? -}
-- Find Lmin.

-- LminL = ir/f
--
-- The lowest audible frequency demands the largest table size...
--
-- Lmin = ir/20
--
-- And we select the sampling rate that will cover the highest audible
-- frequencies...
--
-- Lmin = 40,000 * i / 20 = 2000 * i
--
-- Finally, we need to be able to increment by at least 1...
--
-- i = Lmin/2000 -> Lmin = 2000 samples



{- Exercise 18.10: The Doppler Effect occurs when a sound source is in motion.
 - For example, as a police car moves toward you, its siren sounds higher than
 - it really is, and as it goes past you, it sounds lower. How fast would a
 - police car have to go to change a siren whose frequency is the same as
 - concert A (440Hz) to a pitch an octave higher (i.e. twice the frequency)? At
 - that speed, what frequency would you hear after the police car passes you?-}

-- Let f' = percieved frequency
--     f0 = source frequency
--     v  = 768 miles/hr    -(speed of sound)
--     vs = source velocity
--
-- f' = f0 * (v / (v - vs))
--
-- The source velocity scales the perceived frequency.
--
--
-- 880 = 440 * (768 / (768 - vs))
--  vs = 384 mph
--
-- f' = 440 * (768 / (768 - (-384)))
-- f' = 293 Hz
--
