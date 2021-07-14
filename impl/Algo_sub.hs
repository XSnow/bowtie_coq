{-
    Algo_sub.hs
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

module SubtypingAlgorithm where


data Type = TInt
          | TTop
          | TBot
          | TArrow Type Type
          | TAnd Type Type
          | TOr Type Type
          deriving (Eq, Show)



-- ordinary type

ordinaryI :: Type -> Bool
ordinaryI a = splitI a == Nothing

ordinaryU :: Type -> Bool
ordinaryU a = splitU a == Nothing



-- split type

splitI :: Type -> Maybe (Type, Type)

splitI (TAnd a b) = Just (a, b)
splitI (TArrow a b)
  | Just (b1, b2) <- splitI b
  = Just (TArrow a b1, TArrow a b2)
splitI (TArrow a b)
  | Just (a1, a2) <- splitU a
  = Just (TArrow a1 b, TArrow a2 b)
splitI (TOr a b)
  | Just (a1, a2) <- splitI a
  = Just (TOr a1 b, TOr a2 b)
splitI (TOr a b)
  | Just (b1, b2) <- splitI b
  = Just (TOr a b1, TOr a b2)
splitI _ = Nothing


splitU :: Type -> Maybe (Type, Type)

splitU (TOr a b) = Just (a, b)
splitU (TAnd a b)
  | Just (a1, a2) <- splitU a
  = Just (TAnd a1 b, TAnd a2 b)
splitU (TAnd a b)
  | Just (b1, b2) <- splitU b
  = Just (TOr a b1, TOr a b2)
splitU _ = Nothing




-- subtyping

checkSub :: Type -> Type -> Bool
checkSub TInt TInt = True                                                          -- AS-int
checkSub _ TTop    = True                                                          -- AS-top
checkSub TBot _    = True                                                          -- AS-bot
checkSub a b                                                                       -- AS-and
  | Just (b1, b2) <- splitI b
  = checkSub a b1 && checkSub a b2
checkSub a b                                                                       -- AS-andL AS-andR
  | Just (a1, a2) <- splitI a
  = checkSub a1 b || checkSub a2 b
checkSub a b                                                                       -- AS-or
  | Just (a1, a2) <- splitU a
  = checkSub a1 b && checkSub a2 b
checkSub a b                                                                       -- AS-orL AS-orR
  | Just (b1, b2) <- splitU b
  = checkSub a b1 || checkSub a b2
checkSub (TArrow a1 a2) (TArrow b1 b2)                                             -- AS-arrow
  = checkSub b1 a1 && checkSub a2 b2
checkSub _ _ = False




-- for testing
-- pretty printer
pretty :: Type-> String
pretty (TAnd a b) = "(" ++ pretty a ++ " /" ++ "\\" ++ " " ++ pretty b ++ ")"
pretty (TOr a b) = "(" ++ pretty a ++ " \\" ++ "/ " ++ pretty b ++ ")"
pretty (TArrow a b) = "(" ++ pretty a ++ " -> " ++ pretty b ++ ")"
pretty TInt = "Int"
pretty TTop = "Top"
pretty TBot = "Bot"


showtest :: Type -> Type -> String
showtest a b =
  pretty a ++ " <: " ++ pretty b ++ "  Result: " ++ show (checkSub a b)



-- examples
t0 = TArrow TInt TInt
t1 = (TArrow (TInt) (TAnd TInt TInt))
t2 = TArrow (TOr TInt t0) TInt
t3 = TAnd (TArrow t0 TInt) (TArrow TInt TInt)

test1 = showtest t1 t1                                                              -- True

test3 = showtest t2 t3                                                              -- True
test4 = showtest TBot TInt                                                          -- True
test5 = showtest (TArrow TInt TTop) t0                                              -- False
test6 = showtest t0 (TArrow TInt TTop)                                              -- True

test10 = showtest (TAnd t0 TInt) (TAnd t0 TInt)                                     -- True
test11 = showtest (TOr t0 TInt) (TOr t0 TInt)                                       -- True

test12 = showtest (TAnd t0 TInt) t0                                                 -- True
test13 = showtest t0 (TAnd t0 TInt)                                                 -- False
test14 = showtest (TOr t0 TInt) t0                                                  -- False
test15 = showtest t0 (TOr t0 TInt)                                                  -- True
