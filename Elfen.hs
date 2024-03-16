module Elfen where

import qualified Data.Map as Map
import qualified Control.Monad as Monad
import qualified Data.Char as Char
import qualified Data.Maybe as Maybe
import qualified System.IO

{-
Lexical/static scope seems a good idea but Lisp complicates things
Dynamic scope is easy - just have memory map each symbol to a value
For lexical scope, different occurrences of symbols must be mapped to different values at any one time
-}

type Environment = Map.Map Symbol Value

data Constant =
    Character Char
  | Integer Integer deriving Eq

instance Show Constant where
  show (Character c) = [c]
  show (Integer n) = show n

type Symbol = String

data Value =
    Symbol Symbol
  | Cons Value Value
  | Nil
  | Constant Constant
  | Abstraction Value [Symbol] Environment
  | Primitive Primitive deriving Eq

instance Show Value where
  show (Symbol s) = s
  show c@(Cons _ _) = showList' c
  show Nil = showList' Nil
  show (Constant c) = show c
  show (Abstraction _ _ _) = "<Abstraction>"
  show (Primitive p) = "<Primitive " ++ show p ++ ">"

showList' :: Value -> String
showList' v = '(' : f v
 where f Nil = ")"
       f (Cons x y@(Cons _ _)) = show x ++ " " ++ f y
       f (Cons x y) = show x ++ f y
       f x = " . " ++ show x ++ ")"

-- identity monad for now
newtype M a = Mu {mu :: a}

instance Functor M where
  fmap = Monad.liftM

instance Applicative M where
  pure x = Mu x
  (<*>) = Monad.ap 

instance Monad M where
  (Mu mx) >>= mf = mf mx
--return = pure

{-
return a >>= k
= Mu a >>= k
= k a

(Mu mx) >>= return
= return mx
= Mu mx

(Mu mx) >>= (\x -> k x >>= h)
= (\x -> k x >>= h) mx
= k mx >>= h
= ((Mu mx) >>= k) >>= h
-}



bind :: Symbol -> Value -> Environment -> Environment
bind s v e = Map.insert s v e

eval :: Value -> Environment -> M Value
eval (Symbol s) e = pure $ (Map.findWithDefault) (error $ "Symbol has no definition: " ++ show s) s e
eval (Cons x y) e = evalApplication x y e
eval Nil _ = pure Nil
eval (Constant c) _ = pure (Constant c)
eval _ _ = error "Evaluating an applicable value outside of an application"

evalApplication :: Value -> Value -> Environment -> M Value
evalApplication (Symbol x) y e -- check for special forms
 | Map.member x specialOperators = (Map.!) specialOperators x y e
evalApplication x y e = do
  x' <- eval x e
  y' <- evalList y e
  apply x' y'

evalList :: Value -> Environment -> M [Value]
evalList Nil _ = pure []
evalList (Cons x y) e = do
  x' <- eval x e
  y' <- evalList y e
  pure (x' : y')
evalList _ _ = error "Evaluating a non-list as a list"

apply :: Value -> [Value] -> M Value
apply (Primitive x) ys = applyPrimitive x ys
apply (Abstraction x ss e) ys = (defineList (matchingZip ss ys) e) >>= \e' -> eval x e'
  where matchingZip [] [] = []
        matchingZip (x':xs') (y':ys') = (x', y') : matchingZip xs' ys'
        matchingZip _ _ = error "different number of arguments and parameters"
apply _ _ = error "Applying a non-applicable value"

-- give a symbol a new value binding
define :: Symbol -> Value -> Environment -> M Environment
define s v e = pure $ bind s v e

defineList :: [(Symbol, Value)] -> Environment -> M Environment
defineList [] e = pure e
defineList ((x, y):zs) e = do
  e' <- define x y e
  defineList zs e'

data Primitive = CONS | CF | CS
 | PLUS | MINUS | EQN
 | Y deriving (Eq, Show)

applyPrimitive :: Primitive -> [Value] -> M Value
applyPrimitive CONS [x,y] = pure $ Cons x y
applyPrimitive CF [Cons x _] = pure $ x
applyPrimitive CS [Cons _ y] = pure $ y
applyPrimitive PLUS [Constant (Integer x), Constant (Integer y)] = pure $ Constant $ Integer (x + y)
applyPrimitive MINUS [Constant (Integer x), Constant (Integer y)] = pure $ Constant $ Integer (x - y)
applyPrimitive EQN [Constant (Integer x), Constant (Integer y)] = pure $ if x == y then Symbol "t" else Nil
applyPrimitive o vs = error $ "Wrong argument type (s) for primitive operator: " ++ show o ++ " of " ++ show vs
 
{- I pick out special operators at symbol level rather than value level - it will not be possible to evaluate anything but some predetermined symbols into special operators, which is in accordance with typical Lisps and will make checking easier (it's hard to imagine what type a special operator might have). -}
specialOperators :: Map.Map Symbol (Value -> Environment -> M Value)
specialOperators = Map.fromList
                   [("quote", (\(Cons v _) _ -> pure v)),
                    ("lam", (\(Cons params (Cons body Nil)) e -> pure (Abstraction body (map asSymbol $ unElfenList params) e))),
                    ("if", (\(Cons test (Cons true (Cons false Nil))) e -> eval test e >>= (\r -> if r == Nil then eval false e else eval true e))),
                    ("fix", fixOperator),
                    ("apply", (\(Cons f (Cons xs Nil)) e -> eval f e >>= \f' -> evalList xs e >>= \xs' -> apply f' xs'))]

{-
(fix (x X) body) -> ((lam (x) body) (Y (lam (x) X)))
(fix (x X ... z Z) body) -> (apply (lam (x ... z) body) (Y' (lam (x ... z) X) ... (lam (x ... z) Z)))
-}
fixOperator :: Value -> Environment -> M Value
fixOperator (Cons defs (Cons body Nil)) e =
  let ds' = pairUp $ unElfenList defs in
    let ds = map (\(s, v) -> (asSymbol s, v)) ds' in
      let ss = map fst ds in
        let ods = map (\(s, v) -> (s, Cons (Symbol "lam") (Cons (elfenList $ map Symbol ss) (Cons v Nil)))) ds in
          let odsnds = map snd ods in
            let f ((s, v):xs) e = eval (Cons v $ elfenList odsnds) e >>= (\v' -> define s v' e >>= (\e' -> f xs e'))
                f [] e = pure e in
              f ods e >>= eval body

{-
-- from https://okmij.org/ftp/Computation/fixed-point-combinators.html
(\l -> Y (\self -> map ($ self) l)) [f, g, h]
= Y (\self -> map ($ self) [f, g, h])
= Y (\self -> [f self, g self, h self])
= (\self -> [f self, g self, h self]) (Y (\self -> [f self, g self, h self]))
= [f (Y (\self -> [f self, g self, h self])), g (Y (\self -> [f self, g self, h self])), h (Y (\self -> [f self, g self, h self]))]

fixOperator {((* (lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m)))))
     (* 6 5))} e
= let ds' = pairUp $ unElfenList {(* (lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m)))))} in
    let ds = map (\(s, v) -> (asSymbol s, v)) ds' in
      let ss = map fst ds in
        let ods = map (\(s, v) -> (s, Cons (Symbol "lam") (Cons (elfenList $ map Symbol ss) (Cons v Nil)))) ds in
          let odsnds = map snd ods in
            let f ((s, v):xs) e = eval (Cons v $ elfenList odsnds) e >>= (\v' -> define s v' e >>= (\e' -> f xs e'))
                f [] e = pure e in
              f ods e >>= eval {(* 6 5)}
= let ds = map (\(s, v) -> (asSymbol s, v)) [({*}, {(lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m))))})] in
      let ss = map fst ds in
        let ods = map (\(s, v) -> (s, Cons (Symbol "lam") (Cons (elfenList $ map Symbol ss) (Cons v Nil)))) ds in
          let odsnds = map snd ods in
            let f ((s, v):xs) e = eval (Cons v $ elfenList odsnds) e >>= (\v' -> define s v' e >>= (\e' -> f xs e'))
                f [] e = pure e in
              f ods e >>= eval {(* 6 5)}
= let ss = map fst [("*", {(lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m))))})] in
        let ods = map (\(s, v) -> (s, Cons (Symbol "lam") (Cons (elfenList $ map Symbol ss) (Cons v Nil)))) [("*", {(lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m))))})] in
          let odsnds = map snd ods in
            let f ((s, v):xs) e = eval (Cons v $ elfenList odsnds) e >>= (\v' -> define s v' e >>= (\e' -> f xs e'))
                f [] e = pure e in
              f ods e >>= eval {(* 6 5)}
= let ods = map (\(s, v) -> (s, Cons (Symbol "lam") (Cons (elfenList $ map Symbol ["*"]) (Cons v Nil)))) [("*", {(lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m))))})] in
    let odsnds = map snd ods in
      let f ((s, v):xs) e = eval (Cons v $ elfenList odsnds) e >>= (\v' -> define s v' e >>= (\e' -> f xs e'))
          f [] e = pure e in
        f ods e >>= eval {(* 6 5)}
= let ods = [("*", {(lam (*) (lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m)))))})] in
    let odsnds = map snd ods in
      let f ((s, v):xs) e = eval (Cons v $ elfenList odsnds) e >>= (\v' -> define s v' e >>= (\e' -> f xs e'))
          f [] e = pure e in
        f ods e >>= eval {(* 6 5)}
= let odsnds = map snd [("*", {(lam (*) (lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m)))))})] in
    let f ((s, v):xs) e = eval (Cons v $ elfenList odsnds) e >>= (\v' -> define s v' e >>= (\e' -> f xs e'))
        f [] e = pure e in
      f [("*", {(lam (*) (lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m)))))})] e >>= eval {(* 6 5)}
= let odsnds = [{(lam (*) (lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m)))))}] in
    let f ((s, v):xs) e = eval (Cons v $ elfenList odsnds) e >>= (\v' -> define s v' e >>= (\e' -> f xs e'))
        f [] e = pure e in
      f [("*", {(lam (*) (lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m)))))})] e >>= eval {(* 6 5)}
= let f ((s, v):xs) e = eval (Cons v $ elfenList [{(lam (*) (lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m)))))}]) e >>= (\v' -> define s v' e >>= (\e' -> f xs e'))
      f [] e = pure e in
    f [("*", {(lam (*) (lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m)))))})] e >>= eval {(* 6 5)}
= let f ((s, v):xs) e = eval (Cons v $ elfenList [{(lam (*) (lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m)))))}]) e >>= (\v' -> define s v' e >>= (\e' -> f xs e'))
      f [] e = pure e in
    (eval (Cons {(lam (*) (lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m)))))} $ elfenList [{(lam (*) (lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m)))))}]) e >>= (\v' -> define "*" v' e >>= (\e' -> f [] e'))) >>= eval {(* 6 5)}
= let f ((s, v):xs) e = eval (Cons v $ elfenList [{(lam (*) (lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m)))))}]) e >>= (\v' -> define s v' e >>= (\e' -> f xs e'))
      f [] e = pure e in
    (eval (Cons {(lam (*) (lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m)))))} $ elfenList [{(lam (*) (lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m)))))}]) e >>= (\v' -> define "*" v' e >>= (\e' -> pure e'))) >>= eval {(* 6 5)}
= (eval (Cons {(lam (*) (lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m)))))} $ elfenList [{(lam (*) (lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m)))))}]) e >>= (\v' -> define "*" v' e >>= (\e' -> pure e'))) >>= eval {(* 6 5)}
= (eval {((lam (*) (lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m))))) (lam (*) (lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m))))))} e >>= (\v' -> define "*" v' e >>= (\e' -> pure e'))) >>= eval {(* 6 5)}
= (eval {((lam (*) (lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m))))) (lam (*) (lam (n m) (if (eqn n 0) 0 (+ m (* (+ n -1) m))))))} e >>= (\v' -> define "*" v' e >>= (\e' -> pure e'))) >>= eval {(* 6 5)}

-}

unElfenList :: Value -> [Value]
unElfenList Nil = []
unElfenList (Cons x xs) = x: unElfenList xs

elfenList :: [Value] -> Value
elfenList (v:vs) = Cons v $ elfenList vs
elfenList [] = Nil

pairUp :: [a] -> [(a, a)]
pairUp (x:y:xs) = (x,y) : pairUp xs
pairUp [] = []

asSymbol :: Value -> Symbol
asSymbol (Symbol s) = s

initialState :: Environment
initialState = mu (defineList initialDefinitions Map.empty)
 where initialDefinitions =
         [("+", Primitive PLUS),
          ("eqn", Primitive EQN),
          ("t", Symbol "t"),
          ("nil", Nil)]

evalSequential :: [Value] -> Environment -> M [Value]
evalSequential [] _ = pure []
evalSequential (x:y) e = do
  x' <- eval x e
  y' <- evalSequential y e
  pure (x' : y')

enterEval :: [Value] -> [Value]
enterEval vs = let initialEnv = initialState in
  mu (evalSequential vs initialEnv) 

data Token = LeftParenthesis | RightParenthesis
  | SymbolLiteral String
  | StringLiteral String
  | IntegerLiteral Integer
  | Apostrophe deriving Show

tokenise :: String -> [Token]
tokenise [] = []
tokenise ('(':cs) = LeftParenthesis : tokenise cs
tokenise (')':cs) = RightParenthesis : tokenise cs
tokenise ('\'':cs) = Apostrophe : tokenise cs
tokenise (c:cs)
  | Char.isSpace c = tokenise cs
  | Char.isDigit c = let (n, cs') = tokeniseInteger (c:cs) in IntegerLiteral n : tokenise cs'
tokenise ('-':c:cs)
  | Char.isDigit c = let (n, cs') = tokeniseInteger (c:cs) in IntegerLiteral (-n) : tokenise cs'
tokenise ('"':cs) = let (s, cs') = tokeniseString cs in StringLiteral s : tokenise cs'
tokenise cs = let (s, cs') = tokeniseSymbol cs in SymbolLiteral s : tokenise cs'

tokeniseInteger :: String -> (Integer, String)
tokeniseInteger = f 0
  where f acc (c:cs)
          | Char.isDigit c = f (acc * 10 + (toInteger $ Char.digitToInt c)) cs
          | otherwise = (acc, c:cs)

tokeniseString :: String -> (String, String)
tokeniseString cs = let (s, cs') = break (== '"') cs in (s, tail cs')

tokeniseSymbol :: String -> (String, String)
tokeniseSymbol = break (\c -> Char.isSpace c || c == '(' || c == ')')

parseVal :: [Token] -> Maybe (Value, [Token])
parseVal [] = Nothing
parseVal (LeftParenthesis:ts) = parseList ts
parseVal (RightParenthesis:_) = Nothing
parseVal (SymbolLiteral s : ts) = Just (Symbol s, ts)
parseVal (StringLiteral s : ts) = Just (elfenString s, ts)
parseVal (IntegerLiteral s : ts) = Just (Constant (Integer s), ts)
parseVal (Apostrophe : ts) = case parseVal ts of
                               Nothing -> Nothing
                               Just (v, ts') -> Just (Cons (Symbol "quote") (Cons v Nil), ts')

parseList :: [Token] -> Maybe (Value, [Token])
parseList (RightParenthesis:ts) = Just (Nil, ts)
parseList ts = case parseVal ts of
                Nothing -> Nothing
                Just (v, ts') ->
                  case parseList ts' of
                    Nothing -> Nothing
                    Just (v', ts'') -> Just (Cons v v', ts'')

elfenString :: String -> Value
elfenString = foldr Cons Nil . map (Constant . Character)

parse :: [Token] -> Maybe [Value]
parse [] = Just []
parse ts = case parseVal ts of
             Nothing -> Nothing
             Just (v, ts') ->
               case parse ts' of
                 Nothing -> Nothing
                 Just vs -> Just $ v:vs



processFile :: System.IO.Handle -> IO ()
processFile h = do
  ts <- System.IO.hGetContents h
  putStrLn $ unlines $ map show $ enterEval $ Maybe.fromMaybe [Nil] $ parse $ tokenise ts

main :: IO ()
main = do
  i <- getLine
  System.IO.withFile i System.IO.ReadMode processFile
