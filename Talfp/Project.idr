module Project

differences : List Integer -> List Integer
differences [] = []
differences [x] = []
differences (x::y::zs) = y-x :: differences (y::zs)

capitalise : String -> String
capitalise "" = ""
capitalise ts = pack $ [dis] ++ dat
  where
    dis = toUpper $ head $ unpack ts
    dat = map toLower $ tail $ unpack ts
