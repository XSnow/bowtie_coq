{-
    Algo_alt.hs
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

-- Compared with Algo_duo.hs
-- 1) the definition of Type does not depend on Mode
-- 2) no boolean flag is used in Check

module AlternativeDuotypingAlgorithm where


-- TAnd and TOr are two separated constructors

data Type = TInt
          | TTop
          | TBot
          | TArrow Type Type
          | TAnd Type Type
          | TOr Type Type
          deriving (Eq, Show)

data Mode = MSub | MSuper
          deriving (Eq, Show)




-- flip mode (same as in DuotypingAlgorithm)
flipmode :: Mode -> Mode
flipmode MSub = MSuper
flipmode MSuper = MSub


-- select type by mode (same as in DuotypingAlgorithm)
select :: Mode -> Type
select MSub   = TTop
select MSuper = TBot




-- ordinary types (same as in DuotypingAlgorithm)

ordinary :: Mode -> Type -> Bool
ordinary m t = split m t == Nothing



-- split type

split :: Mode -> Type -> Maybe (Type, Type)

split MSub (TAnd a b) = Just (a, b)
split MSub (TArrow a b)
  | Just (b1, b2) <- split MSub b
  = Just (TArrow a b1, TArrow a b2)
split MSub (TArrow a b)
  | ordinary MSub b
  , Just (a1, a2) <- split MSuper a
  = Just (TArrow a1 b, TArrow a2 b)
split MSub (TOr a b)
  | Just (a1, a2) <- split MSub a
  = Just (TOr a1 b, TOr a2 b)
split MSub (TOr a b)
  | ordinary MSub a
  , Just (b1, b2) <- split MSub b
  = Just (TOr a b1, TOr a b2)

split MSuper (TOr a b) = Just (a, b)
split MSuper (TAnd a b)
  | Just (a1, a2) <- split MSuper a
  = Just (TAnd a1 b, TAnd a2 b)
split MSuper (TAnd a b)
  | ordinary MSuper a
  , Just (b1, b2) <- split MSuper b
  = Just (TOr a b1, TOr a b2)

split _ _ = Nothing



-- subtyping / supertyping checking (implemented without the boolean flag)
-- D-arrow is prioritized

check :: Mode -> Type -> Type -> Bool
check _ TInt TInt = True                                   -- D-int
check m _ t
  | select m == t
  = True                                                   -- D-bound
check m t _
  | select (flipmode m) == t
  = True                                                   -- D-bound (dual)
check m (TArrow a1 a2) (TArrow b1 b2)                      -- D-arrow
  = (check (flipmode m) a1 b1) && (check m a2 b2)
check m a b                                                -- D-and
  | Just (b1, b2) <- split m b
  = (check m a b1) && (check m a b2)
check m a b                                                -- D-and (dual)
  | Just (a1, a2) <- split (flipmode m) a
  = (check m a1 b) && (check m a2 b)
check m a b                                                --D-andL D-andR
  | Just (a1, a2) <- split m a
  = (check m a1 b) || (check m a2 b)
check m a b                                                -- D-andL AS-andR (dual)
  | Just (b1, b2) <- split (flipmode m) b
  = (check m a b1) || (check m a b2)
check _ _ _ = False




-- for testing

-- pretty printer
pretty :: Type-> String
pretty (TAnd a b) = "(" ++ pretty a ++ " /" ++ "\\" ++ " " ++ pretty b ++ ")"
pretty (TOr a b) = "(" ++ pretty a ++ " \\" ++ "/ " ++ pretty b ++ ")"
pretty (TArrow a b) = "(" ++ pretty a ++ " -> " ++ pretty b ++ ")"
pretty TInt = "Int"
pretty TTop = "Top"
pretty TBot = "Bot"


showtest :: Mode -> Type -> Type -> String
showtest MSub a b =
  pretty a ++ " <: " ++ pretty b ++ "  Result: " ++ show (check MSub a b)
showtest MSuper a b =
  pretty a ++ " :> " ++ pretty b ++ "  Result: " ++ show (check MSuper a b)


-- examples
t0 = TArrow TInt TInt

t1 = (TArrow (TInt) (TAnd TInt TInt))
test1 = showtest MSub t1 t1                             -- True
test2 = showtest MSuper t1 t1                           -- True

t2 = TArrow (TOr TInt t0) TInt
t3 = TAnd (TArrow t0 TInt) (TArrow TInt TInt)
test3 = showtest MSub t2 t3                             -- True

test4 = showtest MSub TBot TInt                         -- True
test5 = showtest MSuper (TArrow TInt TTop) t0           -- True
test6 = showtest MSuper TBot TInt                       -- False
test7 = showtest MSub (TArrow TInt TTop) t0             -- False

test8 = showtest MSub (TAnd t0 TInt) (TAnd t0 TInt)     -- True
test9 = showtest MSuper (TAnd t0 TInt) (TAnd t0 TInt)   -- True
test10 = showtest MSub (TOr t0 TInt) (TOr t0 TInt)      -- True
test11 = showtest MSuper (TOr t0 TInt) (TOr t0 TInt)    -- True

test12 = showtest MSub (TAnd t0 TInt) t0                -- True
test13 = showtest MSub t0 (TAnd t0 TInt)                -- False
test14 = showtest MSub (TOr t0 TInt) t0                 -- False
test15 = showtest MSub t0 (TOr t0 TInt)                 -- True
