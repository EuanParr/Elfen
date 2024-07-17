module Elfen where

import qualified Data.Map as Map
import qualified Control.Monad as Monad
import qualified Data.Char as Char
import qualified Data.Foldable as Foldable
import qualified Data.Maybe as Maybe
import qualified System.IO
import qualified System.Environment

{-
Lexical/static scope seems a good idea but Lisp complicates things
Dynamic scope is easy - just have memory map each symbol to a value
For lexical scope, different occurrences of symbols must be mapped to different values at any one time
-}

data EnvironmentKey = Term Symbol | Macro Symbol deriving (Eq, Ord, Show)

type Environment = Map.Map EnvironmentKey Value

data Constant =
    Character Char
  | Integer Integer deriving (Eq, Ord)

instance Show Constant where
  show (Character c) = ['<', c, '>']
  show (Integer n) = show n

type Symbol = String

data Value =
    Symbol Symbol
  | Cons Value Value
  | Nil
  | Constant Constant
  | Abstraction Value [Symbol] Environment
  | VarAbstraction Value Symbol Environment
  | Primitive Primitive
  | Quoted Value deriving Eq

instance Show Value where
  show (Symbol s) = s
  show c@(Cons _ _) = showList' c
  show Nil = showList' Nil
  show (Constant c) = show c
  show (Abstraction v ss _) = "<Abstraction " ++ show ss ++ " " ++ show v ++ ">"
  show (VarAbstraction v s _) = "<Abstraction " ++ show s ++ " " ++ show v ++ ">"  
  show (Primitive p) = "<Primitive " ++ show p ++ ">"
  show (Quoted x) = '\'' : show x

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



bind :: EnvironmentKey -> Value -> Environment -> Environment
bind s v env = Map.insert s v env

bindForbidShadow :: EnvironmentKey -> Value -> Environment -> Environment
bindForbidShadow s v env =
  if Map.member s env
  then error ("Forbidden redefining of symbol: " ++ show s)
  else Map.insert s v env

eval :: Value -> Environment -> M Value
eval (Symbol s) env = pure $ (Map.findWithDefault) (error $ "Symbol has no definition: " ++ show s) (Term s) env
eval (Cons x y) e = evalApplication x y e
eval Nil _ = pure Nil
eval (Constant c) _ = pure (Constant c)
eval (Abstraction _ _ _) _ = error "Evaluating an applicable value outside of an application"
eval (VarAbstraction _ _ _) _ = error "Evaluating an applicable value outside of an application"
eval (Primitive _) _ = error "Evaluating an applicable value outside of an application"
eval (Quoted x) _ = pure x

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
apply a@(Abstraction x ss env) ys = (defineList (matchingZip (map Term ss) ys) env) >>= \env' -> eval x env'
  where matchingZip [] [] = []
        matchingZip (x':xs') (y':ys') = (x', y') : matchingZip xs' ys'
        matchingZip _ _ = error $ "different number of arguments and parameters: " ++ show a ++ ", " ++ show ys
apply (VarAbstraction x s env) ys = define (Term s) (elfenList ys) env >>= \env' -> eval x env'
apply a ys = error $ "Applying a non-applicable value " ++ show a ++ " to " ++ show ys

-- give a symbol a new value binding
define :: EnvironmentKey -> Value -> Environment -> M Environment
define s v e = pure $ bind s v e

defineForbidShadow :: EnvironmentKey -> Value -> Environment -> M Environment
defineForbidShadow s v e = pure $ bindForbidShadow s v e

defineList :: [(EnvironmentKey, Value)] -> Environment -> M Environment
defineList [] e = pure e
defineList ((x, y):zs) e = do
  e' <- define x y e
  defineList zs e'

data Primitive = CONS | CF | CS
 | PLUS | MINUS | EQC | EQS | CONSP
 | SYMP | STRTOSYM | SYMTOSTR | LESSTHAN
 | QUOTED | PANIC deriving (Eq, Show)

applyPrimitive :: Primitive -> [Value] -> M Value
applyPrimitive CONS [x,y] = pure $ Cons x y
applyPrimitive CF [Cons x _] = pure $ x
applyPrimitive CS [Cons _ y] = pure $ y
applyPrimitive PLUS [Constant (Integer x), Constant (Integer y)] = pure $ Constant $ Integer (x + y)
applyPrimitive MINUS [Constant (Integer x), Constant (Integer y)] = pure $ Constant $ Integer (x - y)
applyPrimitive EQC [Constant x, Constant y] = pure $ if x == y then Symbol "t" else Nil
applyPrimitive EQS [Symbol x, Symbol y] = pure $ if x == y then Symbol "t" else Nil
applyPrimitive CONSP [Cons _ _] = pure $ Symbol "t"
applyPrimitive CONSP _ = pure $ Nil
applyPrimitive SYMP [Symbol _] = pure $ Symbol "t"
applyPrimitive SYMP [Nil] = pure $ Symbol "t"
applyPrimitive SYMP _ = pure $ Nil
applyPrimitive STRTOSYM [x] = pure $ Symbol $ map (\(Constant (Character c)) -> c) $ unElfenList x
applyPrimitive SYMTOSTR [Symbol x] = pure $ elfenString x
applyPrimitive LESSTHAN [Constant x, Constant y] = pure $ if x < y then Symbol "t" else Nil
applyPrimitive QUOTED [x] = pure $ Quoted x
applyPrimitive PANIC xs = error $ "panicked: " ++ show xs
applyPrimitive o vs = error $ "Wrong argument type (s) for primitive operator: " ++ show o ++ " of " ++ show vs

initialState :: Environment
initialState = mu (defineList initialDefinitions Map.empty)
 where initialDefinitions =
         [(Term "+", Primitive PLUS),
          (Term "eqc", Primitive EQC),
          (Term "eqs", Primitive EQS),
          (Term "consp", Primitive CONSP),
          (Term "cons", Primitive CONS),
          (Term "cf", Primitive CF),
          (Term "cs", Primitive CS),
          (Term "symp", Primitive SYMP),
          (Term "str-to-sym", Primitive STRTOSYM),
          (Term "sym-to-str", Primitive SYMTOSTR),
          (Term "<", Primitive LESSTHAN),
          (Term "quotation", Primitive QUOTED),
          (Term "panic", Primitive PANIC)]
 
{- I pick out special operators at symbol level rather than value level - it will not be possible to evaluate anything but some predetermined symbols into special operators, which is in accordance with typical Lisps and will make checking easier (it's hard to imagine what type a special operator might have). -}
specialOperators :: Map.Map Symbol (Value -> Environment -> M Value)
specialOperators = Map.fromList
                   [("quote", (\(Cons v _) _ -> pure v)),
                    ("lam", (\(Cons params (Cons body Nil)) env ->
                               case params of
                                 Cons _ _ -> pure (Abstraction body (map asSymbol $ unElfenList params) env)
                                 Symbol s -> pure (VarAbstraction body s env)
                            )),
                     ("let", (\(Cons (Cons (Symbol s) (Cons expr Nil)) (Cons body Nil)) env -> eval expr env >>= \expr' -> define (Term s) expr' env >>= \env' -> eval body env')),
                    ("if", (\(Cons test (Cons true (Cons false Nil))) env -> eval test env >>= (\r -> if r == Nil then eval false env else eval true env))),
                    ("letrec2", fixOpTwo),
                    ("letrec", mutualFixOperator),
                    ("apply", (\(Cons f (Cons xs Nil)) env -> eval f env >>= \f' -> evalList xs env >>= \xs' -> apply f' xs')){-,
                    ("freshsym", freshSym)-}]

freshSym :: Value -> Environment -> M Value
freshSym expr env = pure $ Symbol $ sym $ fresh 0 $ add expr (Map.union env $ Map.fromList $ map (\k -> (Term k, Nil)) $ Map.keys specialOperators) where
  add (Symbol s) env' = Map.insert (Term s) Nil env'
  add (Cons x y) env' = add x $ add y env'
  add _ env' = env'
  fresh n env'
    | Map.member (Term $ sym n) env' = fresh (n + 1) env'
    | Map.member (Macro $ sym n) env' = fresh (n + 1) env'
    | otherwise = n
  sym n = "fresh" ++ show n

fixOperator :: Value -> Environment -> M Value
fixOperator (Cons (Cons (Symbol s) (Cons v Nil)) (Cons body Nil)) e = do
  openDef <- eval (elfenList [Symbol "lam", elfenList [Symbol s], v]) e
  recursiveV <- apply yFunction [openDef]
  e' <- define (Term s) recursiveV e
  eval body e'

fixOpTwo :: Value -> Environment -> M Value
fixOpTwo (Cons (Cons (Symbol s) (Cons v (Cons (Symbol s') (Cons v' Nil)))) (Cons body Nil)) e = do
  openDef <- pure (elfenList [Symbol "lam", elfenList [Symbol s, Symbol s'], v])
  openDef' <- pure (elfenList [Symbol "lam", elfenList [Symbol s, Symbol s'], v'])
  listDef <- eval (elfenList [Symbol "lam", elfenList [Symbol "self"], elfenList [Symbol "cons", elfenList [openDef, elfenIndexer 0 (Symbol "self"), elfenIndexer 1 (Symbol "self")], elfenList [Symbol "cons", elfenList [openDef', elfenIndexer 0 (Symbol "self"), elfenIndexer 1 (Symbol "self")], Nil]]]) e
  recursiveV <- apply yFunction [listDef]
  rv <- apply (Primitive CF) [recursiveV]
  rv'' <- apply (Primitive CS) [recursiveV]
  rv' <- apply (Primitive CF) [rv'']
  e' <- define (Term s) rv e
  e'' <- define (Term s') rv' e'
  eval body e''

elfenIndexer :: Integer -> Value -> Value
elfenIndexer n v = elfenList [Symbol "cf", f n v]
  where f 0 v = v
        f n v = elfenList [Symbol "cs", f (n-1) v]

{-
from https://okmij.org/ftp/Computation/fixed-point-combinators.html
(\l -> Y (\self -> map ($ self) l)) [f, g, h]
= Y (\self -> map ($ self) [f, g, h])
= Y (\self -> [f self, g self, h self])
= (\self -> [f self, g self, h self]) (Y (\self -> [f self, g self, h self]))
= [f (Y (\self -> [f self, g self, h self])), g (Y (\self -> [f self, g self, h self])), h (Y (\self -> [f self, g self, h self]))]
-}
mutualFixOperator :: Value -> Environment -> M Value
mutualFixOperator (Cons defs (Cons body Nil)) e =
  let ds' = pairUp $ unElfenList defs in
    let ss = map fst ds' in
      let openDefs = zipWith (\(s, v) n -> (n, s, elfenList [(Symbol "lam"), (elfenList ss), v])) ds' [0..] in
        let aps = map (\(n, s, v) -> elfenList (v : map (\n' -> elfenIndexer n' (Symbol "self")) [0..(toInteger $ length ss - 1)])) openDefs in do
          listDef <- eval (elfenList [Symbol "lam", elfenList [Symbol "self"], elfenListMaker aps]) e
          recursiveV <- apply yFunction [listDef]
          results <- mapM (\(n, _, _) -> Foldable.foldrM (\_ v -> apply (Primitive CS) [v]) recursiveV [1..n] >>= (\v -> apply (Primitive CF) [v])) openDefs
          e' <- defineList (zip (map (Term . asSymbol) ss) results) e
          eval body e'
          --pure $ elfenList results

unElfenList :: Value -> [Value]
unElfenList Nil = []
unElfenList (Cons x xs) = x: unElfenList xs

elfenList :: [Value] -> Value
elfenList (v:vs) = Cons v $ elfenList vs
elfenList [] = Nil

elfenListMaker :: [Value] -> Value
elfenListMaker (v:vs) = elfenList [Symbol "cons", v, elfenListMaker vs]
elfenListMaker [] = Nil

pairUp :: [a] -> [(a, a)]
pairUp (x:y:xs) = (x,y) : pairUp xs
pairUp [] = []

asSymbol :: Value -> Symbol
asSymbol (Symbol s) = s

yFunction :: Value
yFunction = let yPart = elfenList [Symbol "lam", elfenList [Symbol "x"], elfenList [Symbol "f", elfenList [Symbol "x", Symbol "x"]]] in
  mu (eval (elfenList [Symbol "lam", elfenList [Symbol "f"], elfenList [yPart, yPart]]) (Map.empty))

elfenMap :: (Value -> Value) -> Value -> Value
elfenMap f (Cons x y) = Cons (f x) (elfenMap f y)
elfenMap f Nil = Nil

elfenMapM :: (Value -> M Value) -> Value -> M Value
elfenMapM f (Cons x xs) = f x >>= \z -> elfenMapM f xs >>= \zs -> pure $ Cons z zs
elfenMapM f Nil = pure Nil

evalTopLevelSexp :: Value -> Environment -> M (Value, Environment)
evalTopLevelSexp (Cons (Symbol "def") (Cons (Symbol x) (Cons exp Nil))) env =
  eval exp env >>= \v -> defineForbidShadow (Term x) v env >>= \env' -> pure (v, env')
evalTopLevelSexp exp env = eval exp env >>= \v -> pure (v, env)

macroExpandOnce :: Value -> Environment -> M (Value, Bool)
macroExpandOnce v@(Cons (Symbol x) y) env =
  case Map.lookup (Macro x) env of
    Just f -> apply f (unElfenList y) >>= \v' -> pure (v', True)
    Nothing -> pure (v, False)
macroExpandOnce v env = pure (v, False)

-- (note - this uses an eager reduction strategy and macro reduction is not confluent)
macroNormalise :: Value -> Environment -> M Value
macroNormalise v@(Cons _ _) env = elfenMapM (flip macroNormalise env) v >>=
  \z -> macroExpandOnce z env >>=
  \(v', changed) -> if changed then macroNormalise v' env else pure v'
macroNormalise v env = pure v

-- apply macros then process any directives or delegate to evalTopLevelSexp
execTopLevelSexp :: Value -> Environment -> M (Value, Environment)
execTopLevelSexp exp env = macroNormalise exp env >>= \exp' ->
  case exp' of
    (Cons (Symbol "macro") (Cons (Symbol x) (Cons body Nil))) ->
      eval body env >>= \body' -> define (Macro x) body' env >>= \env' -> pure (body', env')
    _ -> evalTopLevelSexp exp' env >>= \(exp'', env') -> pure (exp'', env')

execSexpStream :: [Value] -> Environment -> M ([Value], Environment)
execSexpStream [] env = pure ([], env)
execSexpStream (x:y) env = do
  (x', env') <- execTopLevelSexp x env
  (y', env'') <- execSexpStream y env'
  pure (x' : y', env'')

data Token = LeftParenthesis | RightParenthesis
  | SymbolLiteral String
  | StringLiteral String
  | IntegerLiteral Integer
  | Apostrophe deriving Show

tokenise :: String -> [Token]
tokenise [] = []
tokenise (';':cs) = eatComment cs
  where eatComment ('\n':cs') = tokenise cs'
        eatComment (_:cs') = eatComment cs'
        eatComment [] = tokenise []
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
                               Just (v, ts') -> Just (Quoted v, ts')

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



processFile :: String -> Environment -> IO (String, Environment)
processFile f env =
  System.IO.readFile f >>= \text -> let (vals, env') = mu $ execSexpStream (Maybe.fromMaybe [Nil] $ parse $ tokenise text) env in pure (unlines $ map show vals, env')

-- for now, output all resulting values from the last file given
evalFiles :: [String] -> Environment -> IO ()
evalFiles [] env= putStrLn "Error: unreachable state, should have prelude"
evalFiles [x] env = processFile x env >>= \(exp', _) -> putStrLn exp'
evalFiles (x:xs) env = processFile x env >>= \(_, env') -> evalFiles xs env'

main :: IO ()
main = do
  args <- System.Environment.getArgs
  if args == [] then {-getContents >>= processFile-} putStrLn "Error: no filename given." else evalFiles ("prelude.lfn" : args) initialState
