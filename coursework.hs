{-# OPTIONS_GHC -Wno-incomplete-patterns #-}


------------------------- Auxiliary functions

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys

variables :: [Var]
variables = [ [x] | x <- ['a'..'z'] ] ++ [ x : show i | i <- [1..] , x <- ['a'..'z'] ]

removeAll :: [Var] -> [Var] -> [Var]
removeAll xs ys = [ x | x <- xs , x `notElem` ys ]

fresh :: [Var] -> Var
fresh = head . removeAll variables


------------------------- Assignment 1: Simple types

data Type = Base
          | Type :-> Type
          deriving (Eq)

nice :: Type -> String
nice Base = "o"
nice (Base :-> b) = "o -> " ++ nice b
nice (   a :-> b) = "(" ++ nice a ++ ") -> " ++ nice b

instance Show Type
      
        where show = nice

typeTest::Type
typeTest = Base
type1 :: Type
type1 =  Base :-> Base

type2 :: Type
type2 = (Base :-> Base) :-> (Base :-> Base)



-- - - - - - - - - - - -- Terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var Type Term
  | Apply    Term Term



pretty :: Term -> String
pretty = f 0
    where
      f i (Variable   x) = x
      f i (Lambda x t m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ": " ++ nice t ++ " . " ++ f 0 m
      f i (Apply    n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

instance Show Term where
  show = pretty



-- - - - - - - - - - - -- Numerals


numeral :: Int -> Term

numeral i = Lambda "f" (Base :-> Base) (Lambda "x" Base (numeral' i))
  where
    numeral' i
      | i <= 0    = Variable "x"
      | otherwise = Apply (Variable "f") (numeral' (i-1))



sucterm :: Term
sucterm =
    Lambda "m" type2 (
    Lambda "f" type1 (
    Lambda "x" Base (
    Apply (Apply (Variable "m") (Variable "f"))
          (Apply (Variable "f") (Variable "x"))
    )))

addterm :: Term
addterm =
    Lambda "m" type2 (
    Lambda "n" type2 (
    Lambda "f" type1 (
    Lambda "x" Base (
    Apply (Apply (Variable "m") (Variable "f"))
          (Apply (Apply (Variable "n") (Variable "f")) (Variable "x"))
    ))))

multerm :: Term
multerm =
    Lambda "m" type2 (
    Lambda "n" type2 (
    Lambda "f" type1 (
    Apply (Variable "m") (Apply (Variable "n") (Variable "f"))
    )))

testTerm::Term
testTerm = Lambda "x" typeTest (Lambda "x" typeTest (Variable "x"))

suc :: Term -> Term
suc = Apply sucterm

add :: Term -> Term -> Term
add m = Apply (Apply addterm m)

mul :: Term -> Term -> Term
mul m = Apply (Apply multerm m)

example1 :: Term
example1 = suc (numeral 0)

example2 :: Term
example2 = numeral 2 `mul` suc (numeral 2)

example3 :: Term
example3 = numeral 0 `mul` numeral 10

example4 :: Term
example4 = numeral 10 `mul` numeral 0

example5 :: Term
example5 = (numeral 2 `mul` numeral 3) `add` (numeral 5 `mul` numeral 7)

example6 :: Term
example6 = (numeral 2 `add` numeral 3) `mul` (numeral 3 `add` numeral 2)

example7 :: Term
example7 = numeral 2 `mul` (numeral 2 `mul` (numeral 2 `mul` (numeral 2 `mul` numeral 2)))

example9 :: Term
example9 = Lambda "x" typeTest (Lambda "x" type1 (Variable "x"))

-- - - - - - - - - - - -- Renaming, substitution, beta-reduction
example10 :: Term
example10 = Apply (Lambda "x" typeTest (Lambda "x" type1 (Variable "x"))) (Variable "x")

used :: Term -> [Var]
used (Variable x) = [x]
used (Lambda x b n) = [x] `merge` used n
used (Apply  n m) = used n `merge` used m

rename :: Var -> Var -> Term -> Term
rename x y (Variable z)
    | z == x    = Variable y
    | otherwise = Variable z
rename x y (Lambda z b n)
    | z == x    = Lambda z b n
    | otherwise = Lambda z b (rename x y n)
rename x y (Apply n m) = Apply (rename x y n) (rename x y m)


substitute :: Var -> Term -> Term -> Term
substitute x n (Variable y)
    | x == y    = n
    | otherwise = Variable y
substitute x n (Lambda y b m)
    | x == y    = Lambda y b m
    | otherwise = Lambda z b (substitute x n (rename y z m))
    where z = fresh (used n `merge` used m `merge` [x,y])
substitute x n (Apply m p) = Apply (substitute x n m) (substitute x n p)


beta :: Term -> [Term]
beta (Apply (Lambda x b n) m) = [substitute x m n] ++ [Apply (Lambda x b n') m  | n' <- beta n] ++ [Apply (Lambda x b n)  m' | m' <- beta m]
beta (Apply n m) =
  [Apply n' m  | n' <- beta n] ++
  [Apply n  m' | m' <- beta m]
beta (Lambda x b n) = [Lambda x b n' | n' <- beta n]
beta (Variable _) = []


-- - - - - - - - - - - -- Normalize


it::Term
it = Variable "String"

num::Integer
num = 0;


normalize :: Term -> IO ()

normalize m = do
  putStrLn $ show (bound m) <> ":" <> show m
  let ms = beta m

  if null ms then
    return ()
  else
    normalize (head ms)



------------------------- Assignment 2: Type checking


type Context = [(Var, Type)]


typeof :: Context -> Term -> Type

typeof [] (Variable x) = error ("variable " ++ x ++ " not found")

typeof ((v,t) : contexts) (Variable x)
      | v == x = t
      | otherwise = typeof contexts (Variable x)

typeof context (Apply m n) = case typem of
                                  (t1 :-> t2) -> if typen == t1 then t2 else error "context type error"
                                  _ -> error "context type error"
                              where
                                  typen = typeof context n
                                  typem = typeof context m

typeof context (Lambda var ty m) = ty :-> typeof ((var,ty): context) m



example8 = Lambda "x" Base
         (Apply
         (Apply (Variable "f")
                (Variable "x")) (Variable "x"))

------------------------- Assignment 3: Functionals


data Functional =
    Num Int
  | Fun (Functional -> Functional)

instance Show Functional where
  show (Num i) = "Num " ++ show i
  show (Fun f) = "Fun ??"

fun :: Functional -> Functional -> Functional
fun (Fun f) = f

-- - - - - - - - - - - -- Examples

-- plussix : N -> N
plussix :: Functional
plussix =  Fun (\(Num x) -> Num (x + 6))


x = Num 3;


-- plus : N -> (N -> N)
plus :: Functional
plus = Fun(\(Num x) -> Fun(\(Num y) -> Num (x+y)))

-- twice : (N -> N) -> N -> N
twice :: Functional
twice = Fun (\(Fun f) -> Fun(\(Num n) -> f(f(Num n))))

-- - - - - - - - - - - -- Constructing functionals

dummy :: Type -> Functional
dummy Base = Num 0
dummy (a :-> b)= Fun (\_ -> dummy b)

count :: Type -> Functional -> Int
count Base (Num n) = n
count (a :-> b) (Fun f) = count b (f (dummy a))

increment :: Functional -> Int -> Functional
increment (Num n) x = Num (n+x)
increment (Fun f) n = Fun $ \fun -> increment (f fun) n {- if a functiona is passed, we return a function that applies the function passed
        this breaks the function down to its Num from where we able to increment it.
    -}


------------------------- Assignment 4 : Counting reduction steps

type Valuation = [(Var , Functional)]

interpret :: Context -> Valuation -> Term -> Functional

interpret context [] (Variable x) = error "no valuation provided"

interpret context ((var, fun): valuation) (Variable x)
  | var == x = fun
  | otherwise = interpret context valuation (Variable x)

interpret context valuation (Apply m n) =  case interpret context valuation m  of
                                              (Fun f) -> let g = interpret context valuation n in
                                                increment (f g)
                                               (1 + count (typeof context n ) g)

interpret context valuation (Lambda var ty m) = Fun (\func -> interpret ((var, ty) : context) ((var, func): valuation) m)


bound :: Term -> Int
bound t = count ( typeof [] t) (interpret [] [] t)



