data Type = TInt
          | TTop
          | TBot
          | TArrow Type Type
          | TAnd Type Type
          | TOr Type Type
          deriving (Eq, Show)

data Mode = MSub | MSuper
          deriving (Eq, Show)



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



-- ordinary types

ordinary :: Mode -> Type -> Bool
ordinary m t = split m t == Nothing


-- flip mode
flipmode :: Mode -> Mode
flipmode MSub = MSuper
flipmode MSuper = MSub


-- select type by mode
select :: Mode -> Type
select MSub   = TTop
select MSuper = TBot


-- subtyping

check :: Mode -> Type -> Type -> Bool
check _ TInt TInt = True                                                        -- D-int
check m _ t
  | select m == t
  = True                                                                        -- D-bound
check m t _
  | select (flipmode m) == t
  = True                                                                        -- D-bound (dual)
check m (TArrow a1 a2) (TArrow b1 b2)                                           -- D-arrow
  = (check (flipmode m) a1 b1) && (check m a2 b2)
check m a b                                                                     -- D-and
  | Just (b1, b2) <- split m b
  = (check m a b1) && (check m a b2)
check m a b                                                                     -- D-and (dual)
  | Just (a1, a2) <- split (flipmode m) a
  = (check m a1 b) && (check m a2 b)
check m a b                                                                     --D-andL D-andR
  | Just (a1, a2) <- split m a
  = (check m a1 b) || (check m a2 b)
check m a b                                                                     -- D-andL AS-andR (dual)
  | Just (b1, b2) <- split (flipmode m) b
  = (check m a b1) || (check m a b2)     
check _ _ _ = False


-- Pretty printer
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
test1 = showtest MSub t1 t1             -- True
test2 = showtest MSuper t1 t1           -- True

t2 = TArrow (TOr TInt t0) TInt
t3 = TAnd (TArrow t0 TInt) (TArrow TInt TInt)
test3 = showtest MSub t2 t3             -- True

test4 = showtest MSub TBot TInt         -- True
test5 = showtest MSuper (TArrow TInt TTop) t0   -- True
test6 = showtest MSuper TBot TInt         -- False
test7 = showtest MSub (TArrow TInt TTop) t0   -- False
