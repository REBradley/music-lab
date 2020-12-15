module LGrammar where

import Euterpea


data DetGrammar a = DetGrammar a         -- start symbol
                               [(a,[a])] -- productions

detGenerate :: Eq a => DetGrammar a -> [[a]]
detGenerate (DetGrammar st ps) = iterate (concatMap f) [st]
  where f a = maybe [a] id (lookup a ps)

redAlgae = DetGrammar 'a'
  [('a',"b|c"), ('b',"b"), ('c',"b|d"),
   ('d',"e\\d"), ('e',"f"),('f',"g"), 
   ('g',"h(a)"), ('h',"h"),('|', "|"),
   ('(',"("), (')',")"), ('/',"\\"),
   ('\\',"/")
  ]

pp n g = sequence_ (map putStrLn (take n (detGenerate g)))

{- 13.1 -}

strToMusic :: AbsPitch -> Dur -> String -> Music AbsPitch
strToMusic _  _ []     = rest 0
strToMusic ap d (c:cs) = charToNote c :+: updatedStrToMusic cs
  where charToNote x = maybe (rest 0) id $
                         lookup x [('a', note d ap), ('b', note d $ ap+2)
                               ,('c', note d $ ap+4), ('d', note d $ ap+5)
                               ,('e', note d $ ap+7), ('f', note d $ ap+9)
                               ,('g', note d $ ap+11), ('h', note d $ ap+12)
                               ,('|', rest 0), ('/', rest d)
                               ,('\\', rest d), ('(', rest 0)
                               ,(')', rest 0)
                               ]
        updatedStrToMusic = case c of 
                              '(' -> strToMusic (ap + 5) d
                              ')' -> strToMusic (ap - 5) d
                              _   -> strToMusic ap d
