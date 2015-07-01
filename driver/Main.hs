-- | Driver for testing out the language and transformations on it.
module Main where

import Control.Monad.Except
import Control.Monad.State
import Data.Char
import Text.Parsec

import Distill.Expr
import Distill.UniqueName

type InterpretM = StateT InterpretState IO

data InterpretState = InterpretState
    { assumed :: [(UniqueName, Type)]
    , defined :: [(UniqueName, Expr)]
    , unique :: Int
    }

startInterpretState :: InterpretState
startInterpretState = InterpretState
    { assumed = []
    , defined = []
    , unique = 0
    }

parseExprFromLine :: String -> Either String (Expr' String)
parseExprFromLine line = do
    let parsed = parse (parseExpr "%No-Name%" parseVar <* eof) "<stdin>" line
    case parsed of
        Left err -> throwError (show err)
        Right expr -> return expr
  where
    parseVar = many1 (satisfy isAlphaNum)

printHelp :: IO ()
printHelp = putStrLn $
       "Available commands:\n"
    ++ "  help - Print this help message.\n"
    ++ "  define <name> <expr> - Define an expression."
    ++ "  context - Show the expressions defined so far."

defineExpr :: String -> String -> StateT InterpretState (Either String) ()
defineExpr name unparsed = do
    exprStr <- case parseExprFromLine unparsed of
        Left err -> throwError err
        Right exprStr -> return exprStr
    case freeVars exprStr of
        [] -> return ()
        xs -> throwError $ "Expression contained unbound variables: " ++ show xs

    start <- unique <$> get
    let expr = renumber UniqueName start [] exprStr
    let end = nextAvailableUnique expr
    modify (\s -> s {unique = end})

    assumed_ <- assumed <$> get
    defined_ <- defined <$> get
    type_ <- case runTCM (inferType expr) assumed_ defined_ of
        Left err -> throwError err
        Right type_ -> return type_
    uniqueName <- UniqueName name . unique <$> get
    modify (\s -> s {unique = succ (unique s)})
    modify (\s -> s {assumed = (uniqueName, type_) : assumed_})
    modify (\s -> s {defined = (uniqueName, expr) : defined_})

interpreterLoop :: InterpretM ()
interpreterLoop = do
    command <- lift getLine
    case words command of
        "help":_ -> lift printHelp
        "define":name:expr -> do
            oldState <- get
            case runStateT (defineExpr name (unwords expr)) oldState of
                Left err -> lift . putStrLn $ err
                Right ((), newState) -> put newState
        "define":_ -> lift . putStrLn $ "Must specify an name and expression "
                                     ++ "to defined."
        "context":_ -> do
            defined_ <- defined <$> get
            flip mapM_ defined_ $ \(name, expr) -> do
                lift . putStr $ "define "
                lift . print $ pprUnique name
                lift . putStr $ " "
                lift . print $ pprExpr pprUnique expr
        cmd:_ -> do
            lift . putStrLn $ "Unknown command '" ++ cmd ++ "'."
        [] -> return ()

main :: IO ()
main = runInterpreter startInterpretState
  where
    runInterpreter state = do
        newState <- execStateT interpreterLoop state
        runInterpreter newState
