{-
    Algo_duo.hs
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


module DuotypingAlgorithm where



-- subtyping or supertyping

data Mode = MSub | MSuper
          deriving (Eq, Show)



-- MSub for type intersection, MSuper for type union

data Type = TInt | TTop | TBot | TArrow Type Type | TOp Mode Type Type
          deriving (Eq, Show)



-- flip the mode

flipmode :: Mode -> Mode
flipmode MSub = MSuper
flipmode MSuper = MSub



-- select a type by a mode

select :: Mode -> Type
select MSub   = TTop
select MSuper = TBot



-- ordinary types

ordinary :: Mode -> Type -> Bool
ordinary m t = split m t == Nothing


-- split a type under a mode

split :: Mode -> Type -> Maybe (Type, Type)
split MSub (TArrow a b)                         -- Sp-arrowR
  | Just (b1, b2) <- split MSub b
  = Just (TArrow a b1, TArrow a b2)
split MSub (TArrow a b)                         -- Sp-arrowL
  | Just (a1, a2) <- split MSuper a
  = Just (TArrow a1 b, TArrow a2 b)
split m (TOp m' a b)                            -- Sp-and
  | m == m'
  = Just (a, b)
split m (TOp m' a b)                            -- Sp-orL
  | Just (a1, a2) <- split m a
  = Just (TOp m' a1 b, TOp m' a2 b)
split m (TOp m' a b)                            -- Sp-orR
  | Just (b1, b2) <- split m b
  = Just (TOp m' a b1, TOp m' a b2)
split _ _ = Nothing



-- subtyping / supertyping checking
-- (initally the boolean flag should be False)

check :: Mode -> Type -> Type -> Bool -> Bool
check _ TInt TInt _ = True                                                      -- AD-int
check m _ t _
  | select m == t
  = True                                                                        -- AD-bound
check m a b _                                                                   -- AD-and
  | Just (b1, b2) <- split m b
  = (check m a b1 False) && (check m a b2 False)
check m a b _                                                                   -- AD-andL AD-andR
  | Just (a1, a2) <- split m a
  = (check m a1 b False) || (check m a2 b False)
check m a b False = check (flipmode m) b a True                                 -- AD-dual
check m (TArrow a1 a2) (TArrow b1 b2) _                                         -- AD-arrow
  = (check (flipmode m) a1 b1 False) && (check m a2 b2 False)
check _ _ _ _ = False




-- for testing

-- pretty printer

pretty :: Type-> String
pretty (TOp MSub a b) = "(" ++ pretty a ++ " /" ++ "\\" ++ " " ++ pretty b ++ ")"
pretty (TOp MSuper a b) = "(" ++ pretty a ++ " \\" ++ "/ " ++ pretty b ++ ")"
pretty (TArrow a b) = "(" ++ pretty a ++ " -> " ++ pretty b ++ ")"
pretty TInt = "Int"
pretty TTop = "Top"
pretty TBot = "Bot"


showtest :: Mode -> Type -> Type -> String
showtest MSub a b =
  pretty a ++ " <: " ++ pretty b ++ "  Result: " ++ show (check MSub a b False)
showtest MSuper a b =
  pretty a ++ " :> " ++ pretty b ++ "  Result: " ++ show (check MSuper a b False)


-- examples

t0 = TArrow TInt TInt

t1 = (TArrow (TInt) (TOp MSub TInt TInt))
test1 = showtest MSub t1 t1                                                     -- True
test2 = showtest MSuper t1 t1                                                   -- True

t2 = TArrow (TOp MSuper TInt t0) TInt
t3 = TOp MSub (TArrow t0 TInt) (TArrow TInt TInt)
test3 = showtest MSub t2 t3                                                     -- True

test4 = showtest MSub TBot TInt                                                 -- True
test5 = showtest MSuper (TArrow TInt TTop) t0                                   -- True
test6 = showtest MSuper TBot TInt                                               -- False
test7 = showtest MSub (TArrow TInt TTop) t0                                     -- False

test8 = showtest MSub (TOp MSub t0 TInt) (TOp MSub t0 TInt)                     -- True
test9 = showtest MSuper (TOp MSub t0 TInt) (TOp MSub t0 TInt)                   -- True
test10 = showtest MSub (TOp MSuper t0 TInt) (TOp MSuper t0 TInt)                -- True
test11 = showtest MSuper (TOp MSuper t0 TInt) (TOp MSuper t0 TInt)              -- True

test12 = showtest MSub (TOp MSub t0 TInt) t0                                    -- True
test13 = showtest MSub t0 (TOp MSub t0 TInt)                                    -- False
test14 = showtest MSub (TOp MSuper t0 TInt) t0                                  -- False
test15 = showtest MSub t0 (TOp MSuper t0 TInt)                                  -- True
