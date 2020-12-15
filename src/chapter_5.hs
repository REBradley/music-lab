import Euterpea

{--EXERCISE 5.1: Define a funtion twice that, given a function f, returns a
 - function that applies f twice to it's argument. For example:
 -
 - (twice(+1))2 -> 4
 - 
 - What is the principal type of twice? Describe what twice twice does and give
 - an example of its use. Also consider the functions twice twice twice and 
 - twice (twice twice).
 -      
 -      twice (+2) 5 = (+2) ( (+2) 5 )
 -                   = (+2) ( 5 + 2 )
 -                   = (+2) (7)
 -                   = 9
 -
 -      
 -      twice twice f x = twice (twice  f x) 
 -                      = twice f (f x) 
 -                      = f( f (f (f x) ) )
 -
 -                            
 -
 -      twice twice (+2) 5 = twice ( twice (+2) 5 ) 
 -                         = twice ((+2) ( (+2) 5 ) )
 -                         = (+2)(+2)( (+2) (+2) 5 )
 -                         = 13
 -                         
 -      twice twice twice f x = (twice twice) twice f x
 -                            = twice ( twice twice f x )
 -                            = twice ( twice ( twice f x ) )
 -                            = twice ( twice ( f ( f x) ) )
 -                           = twice ( f ( f ( f ( f x ) ) ) )
 -                          = f f f f f f f f x
 -
 --}
twice :: (a -> a) -> (a -> a)
twice f x = f (f x)


{--EXERCISE 5.2: Generalize twice defined in the previous exercise by defining a
 - function power that takes a function f and an integer n and returns a
 - function that applies the function f to its argument n times. For example:
 -
 - power (+2) 5 1 --> 11
 -
 - Use power in a musical context to define something useful.
 - --}
power :: (a -> a) -> Int -> a -> a
power f 1 x = f x
power f i x = f (power f (i-1) x )



powerThirds                    :: Int -> Music Pitch -> Music Pitch
powerThirds 0 (Prim(Note d p)) = note d p
powerThirds i (Prim(Note d p)) = note d (power (trans 3) i p)


complexHarmony i p = chord ((map ((flip powerThirds) p)) [0..i])


{--EXERCISE 5.3: Suppose we define a function fix as:
 -
 -         fix f = f (fix f)
 -
 - What is the principal type of fix?
 -
 - Suppose further that we have a recursive function:
 - 
 - remainder    :: Integer -> Integer -> Integer
 - remainder a b = if a < b then a
 -                 else remainder (a - b) b
 -
 - Rewrite this function using fix so that there is no recursive call to
 - remainder. Do you think that this process can be applied to any recursive
 - function?
 -
 -
 - Whatever fix takes as an argument can be applied, so we know it's argument is a function.
 -
 - (a -> a) -> a
 -
 - fix returns something that we can apply f on. f can be applied to whatever
 - fix returns 
 -
 -
 -
 -
 -
 -
 -
 -
 -
 -
 -
 -
 -
 -
 - 
 -
 - --}


fix   :: (a -> a) -> a 
fix f = f (fix f)


remainder :: Integer -> Integer -> Integer
remainder a b = fix (\x -> if x < b then x else x - b)



apPairs :: [AbsPitch] -> [AbsPitch] -> [(AbsPitch,AbsPitch)]
apPairs aps1 aps2 = [(ap1,ap2) | ap1 <- aps1, ap2 <- aps2, 
                                 2 < abs(ap1-ap2), 
                                 abs(ap1-ap2) < 8]


playPairs :: [(AbsPitch,AbsPitch)] -> Music Pitch
playPairs aps = line [rythVar ap1 :=: note en (pitch ap2)  | (ap1,ap2) <- aps, 
                let rythVar ap = if odd ap then note wn (pitch ap) else note sn (pitch ap)]


hNote :: Dur -> Pitch -> Music Pitch
hNote d p = note d p :=: note d (trans(-3) p)

hList :: Dur -> [Pitch] -> Music Pitch
hList = \d -> line . map (hNote d)



--EXERCISE 5.6: Use line, map, and ($) to give a concise definition of addDur.

addDur  :: Dur -> [Dur -> Music a] -> Music a
addDur d ns = let f n = n d
              in line (map f ns)

addDur'  :: Dur -> [Dur -> Music a] -> Music a
addDur' d ns = line [n d | n <- ns]


addDur'' :: Dur -> [Dur -> Music a] -> Music a
addDur'' d ns = line $ map (\n -> n d) ns



{--EXERCISE 5.7: Rewrite this example...
 -
 -     map(\x -> (x+1)/2) xs
 -
 - Using a composition of sections --}

add1Halve = map $ (/2) . (+1)

{--EXERCISE 5.8: Consider the expression
 -
 -     map f (map g xs)
 -
 - Rewrite this using function composition and a single call to map. --}


mapFG f g = map $ f . g

mapAddHalve :: (Fractional a) => [a] -> [a]
mapAddHalve xs = map (/2) $ map (+1) xs



{--EXERCISE 5.10:
 -
 - What are f1 and f2?
 -
 -
 - f1 (f2 (*) [1,2,3,4]) 5 --> [5,10,15,20]
 -
 - f1 = map 
 -
 - f2 = \fs x -> map (\f -> f x) fs
 -
 - --}















