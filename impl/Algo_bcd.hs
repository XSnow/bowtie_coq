{-
    Algo_bcd.hs
    Xuejing Huang 2021
    Distributed under the terms of the GPL-v3 license

    This file is part of DistributingTypes.

    DistributingTypes is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    DistributingTypes is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with DistributingTypes.  If not, see <https://www.gnu.org/licenses/>.
-}


module BCDSubtypingAlgorithm where


data Type = TInt
          | TTop
          | TArrow Type Type
          | TAnd Type Type
          deriving (Eq, Show)



-- ordinary type

ordinary :: Type -> Bool
ordinary a = split a == Nothing



-- split type

split :: Type -> Maybe (Type, Type)

split (TAnd a b) = Just (a, b)                           -- Bsp-and
split (TArrow a b)                                       -- Bsp-arrow
  | Just (b1, b2) <- split b
  = Just (TArrow a b1, TArrow a b2)
split _ = Nothing



-- subtyping

checkSub :: Type -> Type -> Bool

checkSub TInt TInt = True                                 -- BS-int
checkSub _ TTop    = True                                 -- BS-top
checkSub a b                                              -- BS-and
  | Just (b1, b2) <- split b
  = checkSub a b1 && checkSub a b2
checkSub (TAnd a1 a2) b                                   -- BS-andL BS-andR
  = checkSub a1 b || checkSub a2 b
checkSub (TArrow a1 a2) (TArrow b1 b2)                    -- BS-arrow
  = checkSub b1 a1 && checkSub a2 b2
checkSub _ _ = False



-- for testing
-- pretty printer
pretty :: Type-> String
pretty (TAnd a b) = "(" ++ pretty a ++ " /" ++ "\\" ++ " " ++ pretty b ++ ")"
pretty (TArrow a b) = "(" ++ pretty a ++ " -> " ++ pretty b ++ ")"
pretty TInt = "Int"
pretty TTop = "Top"


showtest :: Type -> Type -> String
showtest a b =
  pretty a ++ " <: " ++ pretty b ++ "  Result: " ++ show (checkSub a b)



-- examples
t0 = TArrow TInt TInt
t1 = (TArrow (TInt) (TAnd TInt TInt))
t3 = TAnd (TArrow t0 TInt) (TArrow TInt TInt)

test1 = showtest t1 t1                                                              -- True
test2 = showtest (TArrow TInt TTop) t0                                              -- False
test3 = showtest t0 (TArrow TInt TTop)                                              -- True
test4 = showtest (TArrow TInt TTop) (TArrow TTop TTop)                              -- False
test5 = showtest (TAnd t0 TInt) (TAnd t0 TInt)                                      -- True
test6 = showtest t0 (TAnd t0 TInt)                                                  -- False
test7 = showtest (TAnd t0 TInt) t0                                                  -- True
