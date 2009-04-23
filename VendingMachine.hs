{-# LANGUAGE GeneralizedNewtypeDeriving #-}

import Control.Monad
import Control.Concurrent.STM
import GHC.Conc
import Data.Map
import Data.Maybe
import List
import Control.Arrow 
import qualified Control.Exception as E

--For server
import Data.Bits
import Network.Socket
import Network.BSD
import Network
import Data.List
import Control.Concurrent
import Control.Concurrent.MVar
import System.IO
import Data.IORef

--For Parser
import Data.Char
import Text.ParserCombinators.Parsec
import Data.Either
import Text.ParserCombinators.Parsec.Prim

----------------------------------------------------------------------------
-- The Big Picture:
-- This vending machine holds candy and change. It simultaneously services
-- multiple customers and can be restocked real-time. It will block forever if 
-- it cannot make change or does not have enough candy. While a more realistic
-- single user vending machine would refuse to carry out the transaction 
-- and return the customers money , in a multi-user 
-- scenario there is always the chance that someone will come along and either
-- restock the candy/change or buy some candy.
--
-- Additionally this vending machine allows all users to restock it.
--
-- The vending machine is a server process that runs on port 8000 and accepts
-- telnet clients.
--
-- The compilation command is:
--       ghc VendingMachine.hs --make -optl-static -optl-pthread -fforce-recomp
-- Note, this will barf up a bunch of harmless warnings.
--
-- Rough Control Flow:
-- main -> server -> multiple 'procMessages' for each thread
--  Per thread :
--  'procMessages' ->
--     interactiveHandler -> 
--         readCommand -> <some requests are serviced here>
--                    |
--                     -> parseOther <all others are serviced here>
---------------------------------------------------------------------------

data Money = Nickel | Dime | Quarter | Dollar deriving (Ord, Eq, Show, Enum)
type Cost = Int
type Name = String
type Number = Int
type Change = [(Money, Number)]
data Item = Item Name deriving (Show,Ord,Eq)
type Inventory = [(Item,Number)]

type Machine = TVar (Inventory, Change)

divisible :: (Integral a) => a -> a -> Bool
divisible dividend divisor = (dividend `mod` divisor) == 0

upcase :: String -> String
upcase = Data.List.map toUpper

toMoney :: String -> Money
toMoney s = case s of
                "NICKEL" -> Nickel
                "DIME"   -> Dime
                "QUARTER" -> Quarter
                "DOLLAR" -> Dollar

fromMoney :: Money -> String
fromMoney s = case s of
                Nickel  -> "NICKEL" 
                Dime    -> "DIME"   
                Quarter -> "QUARTER"
                Dollar  -> "DOLLAR"

toCandy s = case s of
                "SIXTYFIVE" -> "SixtyFive"
                "DOLLAR"    -> "Dollar"
                "BUCKFIFTY" -> "BuckFifty"

-- Each tuple in the list is an item and its amount 'a'. This function produces a list
-- where each item occurs 'a' times.
-- Eg. [("x",3),("y",4)] => ["x","x","x","y","y","y","y"]
enumList :: [(a,Int)] -> [a]
enumList = concatMap (\x -> replicate (snd x) (fst x))

-- Takes a list of change and coverts it to a numbered list 
-- Eg. [Nickel, Nickel, Dime] => [(Nickel,2),(Dime,1),(Quarter,0),(Dollar,0)]
toNumberedList :: [Money] -> Change
toNumberedList m =
    let emptyList = Data.Map.fromList [(Nickel,0),(Dime,0),(Quarter,0),(Dollar,0)] in
    Data.Map.toList $
        Data.Map.mapWithKey
            (\k v ->  v + ( length $ Data.List.filter (== k) m ) ) emptyList
--             let vs = Data.List.filter (== k) m in
--                        if (not $ Data.List.null vs)
--                          then (v + (length vs))
--                          else v


-- Maps coins to their value
moneyMap :: Data.Map.Map Money Number
moneyMap = Data.Map.fromList [(Quarter, 25),(Nickel, 5),(Dime, 10),(Dollar , 100)]

-- Convert a coin to its value           
currencyConvert :: Money -> Maybe Number
currencyConvert currency = Data.Map.lookup currency moneyMap

-- Maps candy names to cost
candyMap :: Data.Map.Map Name Cost
candyMap = Data.Map.fromList [("SixtyFive" , 65), ("Dollar", 100), ("BuckFifty", 150)]

-- Tallys up a number of coins
-- Eg. [(Nickel,2),(Dime,1),(Quarter,0),(Dollar,0)] => 20
fromCurrency :: Change -> Maybe Number
fromCurrency change = foldM toNumber 0 change
    where
      toNumber balance' (m,am)  =
          do w <- currencyConvert m
             return $ (w * am) + balance'

-- Coins and currency are dispensed from the cashier to the customer.
-- Example, the cashier has [Dollar, Quarter, Dime, Dime, Nickel] and the
-- customer needs $1.40, the output of this function is 
-- Just ([Dollar, Quarter, Dime, Nickel],[Dime]) where the first of the pair
-- is the customer's change and the second is the cashier's leftover.
giveChange :: [Money] -> [Money] -> Number -> Maybe ([Money], [Money])
giveChange cust cashier moneyLeft =
    do
      (good,bad) <- return $ Data.List.partition (\x -> (<= moneyLeft) . fromJust $ currencyConvert x) $ reverse $ sort cashier
      if ((Data.List.null cashier || Data.List.null good) && (moneyLeft > 0))
        then mzero
        else 
          if (moneyLeft == 0)
            then return $ (cust, cashier)
            else do { newCoin <- currencyConvert (head good);
                      giveChange (cust ++ [(head good)])
                                     ((tail good) ++ bad)
                                     (moneyLeft - newCoin)}

balance :: Machine -> STM (Maybe Number)
balance m = do
  (inv, ch) <- readTVar m
  return $ fromCurrency ch

-- Reads the amount of change in the vending machine
currencyStock :: Machine -> STM (Maybe Change)
currencyStock m = do 
  (inv, ch) <- readTVar m
  case ch of
      [] -> return $ Nothing
      x  -> return $ Just x

-- Reads the amount of candy in the vending machine
candyStock :: Machine -> STM (Maybe Inventory)
candyStock m = do
  (inv,ch) <- readTVar m
  return $ Just inv

-- Pure function that modifies the amount of a certain candy according the 'f'
modInv inv c f = do
  x <-  Data.List.lookup (Item c) inv
  return $ Data.Map.toList $ Data.Map.insert (Item c) (f x) $ Data.Map.fromList inv

-- Removes one candy bar from vending machine    
dispenseCandy :: Machine -> Name -> STM ()
dispenseCandy m n = editCandyStock m (\x -> x - 1) n
-- Adds one candy bar to vending machine
addCandy :: Machine -> Name -> STM ()
addCandy m c = editCandyStock m (\x -> x + 1) c

editCandyStock :: Machine -> (Int -> Int) -> Name -> STM ()
editCandyStock m f n = do
  (inv,ch) <- readTVar m
  case modInv inv n f of
      Just a -> writeTVar m (a,ch)
      Nothing -> retry

dispenseChange :: Machine -> Number -> STM (Machine,[Money])
dispenseChange m n = do
  (inv,ch) <- readTVar m
  (zero,actual) <- return $ Data.List.partition ((==0) . snd) ch
  case (giveChange [] (enumList actual) n) of
      Just (a,b) -> do
        writeTVar m (inv,(toNumberedList b) ++ zero)
        return $ (m,a)
      Nothing -> retry

addChange :: Machine -> [Money] -> STM ()
addChange m c = do
  (inv,ch) <- readTVar m
  newCh <- return $ toNumberedList $ c ++ enumList ch
  writeTVar m (inv, newCh)

-----------------------------------------------------------------------------------
-- Modified version of TCP Syslog Server presented in Ch. 27 of "Real World Haskell"
-- For simplicity, the server function currently creates the initial vending machine
-- which gets passed to the incoming client threads.
----------------------------------------------------------------------------------

type Port = String
type HandlerFunc = SockAddr -> String -> IO ()

-- This server grabs a socket and a lock and listens on that socket
-- The lock is only used by the server to log connections to stdout
server :: PortID -> IO ()
server port = withSocketsDo $ 
         do
           sock <- listenOn port
           lock <- newMVar ()
           machine <- atomically testMachine
           procRequests machine lock sock
                            `E.catch` (\e -> putStrLn $ "Exception : " ++ show (e :: E.SomeException))
                            `E.finally` sClose sock
         where
           procRequests :: Machine -> MVar () -> Socket -> IO ()
           procRequests machine lock mastersock = 
               do (connsock, clientaddr) <- Network.Socket.accept mastersock
                  logHandle lock clientaddr
                         "myserver.hs : Client connected"
                  forkIO $ procMessages machine lock connsock clientaddr
                  procRequests machine lock mastersock

-- Used by the server process to log connections. This is the sole use of the lock taken by the server
-- process.
logHandle :: MVar () -> HandlerFunc
logHandle lock clientaddr msg = 
    withMVar lock
               (\a -> (putStrLn $ "From " ++ show clientaddr ++ ": " ++ msg) >> return a)


-- Each incoming client gets a copy of this function. Each client has 
-- their own handle, buffer and cache. The buffer is an infinite list and is read 
-- lazily and each read is passed to a handler. This function returns when hClose is called
--
-- Of note is the cache variable which is a mutable variable local only to this thread that 
-- serves to hold the customers coins until he actually buys something.
procMessages :: Machine -> MVar () -> Socket -> SockAddr -> IO ()
procMessages machine lock connsock clientaddr =
    do connhdl <- socketToHandle connsock ReadWriteMode
       hSetBuffering connhdl LineBuffering
       messages <- hGetContents connhdl
       cache <- newIORef []
       showThreadStatus
       mapM_ (interactiveHandler machine cache lock connhdl clientaddr) (lines messages)
       hClose connhdl
       logHandle lock clientaddr
              "myserver.hs : Client disconnected"

showThreadStatus :: IO ()
showThreadStatus = myThreadId >>= threadStatus >>= (\x -> putStrLn $ "Thread Status :" ++ (show x)) 

-- The main handler for all incoming connections. Its main function is to dispatch incoming messages to 
-- a parsing function and send the resulting message back to the client. The sole exception is "quit" which
-- is dealt with here.
interactiveHandler :: Machine -> IORef [Money] -> MVar () -> Handle -> SockAddr -> String -> IO ()
interactiveHandler machine cache lock handle addr msg =
    (do
       msg' <- return $ Data.List.filter (>= ' ') msg
       m <- readCommand machine msg' cache
       hPutStrLn handle m
       hFlush handle
       case msg' of
           "quit" -> do {hClose handle}
           _ -> return ())
    >> return ()

-- Reads all incoming messages except "quit" which is handled directly by 'interactiveHandler'.
readCommand :: Machine -> String -> IORef [Money] -> IO String
readCommand machine s state = case s of
                          ""                -> return ""
                          "show candystock" -> showCandyStock machine 
                          "show moneystock" -> showMoneyStock machine
                          "show balance"    -> showBalance state
                          "quit"            -> return ""                                                                      
                          "help"            -> return "-Available Commands:\n  insert <Money>\n  show balance | candystock | moneystock\n  restockMoney <Money> \n  restockCandy <Candy>\n  buy <Candy>\n  quit" 
                          _                 -> parseOther machine s state 

showCandyStock machine = showStock machine candyStock    "Candy Stock is empty"
showMoneyStock machine = showStock machine currencyStock "Money Stock is empty"
showBalance    state   = readIORef state >>= (\x -> return $ show x)

-- Show the status of whatever the customer is interested in, candy or coins.
showStock machine f emptyMsg = atomically $ do s' <- f machine
                                               maybe (return $ emptyMsg) (return . show) s'


-- Called only by readCommand, this function actually parses messages that either edit the Vending Machine.
-- This has way more editing code than I would like, but for now it is simpler.
parseOther :: Machine -> String -> IORef [Money] -> IO String
parseOther machine s state = case (head $ words s) of
                         "insert" -> do {x <- return $ Data.List.map toMoney $ snd $ parseResults coinNames;
                                         modifyIORef state ((++) x);
                                         showBalance state}
                         "restockMoney" -> do {x <- return $ Data.List.map toMoney $ snd $ parseResults coinNames;
                                               writeIORef state x;
                                               commitCoins machine state;
                                               showMoneyStock machine}
                         "restockCandy" -> (\candyChoice ->
                                                if (Data.List.null candyChoice)
                                                  then return "restock what?"
                                                  else do
                                                      atomically $ mapM (\x -> addCandy machine (toCandy x)) candyChoice
                                                      showCandyStock machine)
                                           (snd $ parseResults candyNames)
                         "buy"    -> (\candyChoice -> 
                                          if (length candyChoice > 1)
                                            then return "One choice only"
                                            else if (Data.List.null candyChoice)
                                                   then return "Buy What?"
                                                   else buyCandy machine (head candyChoice) state)
                                     (snd $ parseResults candyNames)
                         _        -> return "Cannot understand"
    where
      parseResults parser = (partitionEithers
                             (Data.List.map (parse parser "(unknown)" . upcase) $
                                  tail $ words s))

-- Take coins from the customer's cache and add them to the Vending Machine
commitCoins :: Machine -> IORef [Money] -> IO ()
commitCoins machine m = do
  money' <- readIORef m
  atomically $ addChange machine money'

-- This function coordinates accepting money, removing the candy from stock, and making/returning change.
-- Significantly it accepts the money *before* dispensing candy, this means other clients who are waiting
-- for change don't wait as long. On the other hand, other clients who are waiting on candy have to wait a 
-- little longer. This is based on the assumption that there is a lot more change flowing back and forth 
-- than candy.
buyCandy :: Machine -> Name -> IORef [Money] -> IO String
buyCandy machine candyChoice m = do
  money' <- readIORef m
  cost <- return $ fromJust $ Data.Map.lookup (toCandy candyChoice) candyMap
  if (fromJust $ fromCurrency $ toNumberedList money') >=  cost
    then do
        atomically $ addChange machine money'
        atomically $ dispenseCandy machine (toCandy candyChoice)
        (atomically $ do
           (mch',m') <- dispenseChange machine ((fromJust $ fromCurrency $ toNumberedList money') - cost)
           return m') >>= (\m' -> do {writeIORef m m'; return $ "Candy :" ++ candyChoice ++ " Change: " ++ show m'})
    else return $ "More Money"

-- A parser that accepts money names like "dollar" and "quarter"
coinNames = (foldr ((<|>) . try . string) mzero $ Data.List.map (fromMoney . fst) $ Data.Map.toList moneyMap) <?> "money"
-- A parser that accepts candy names
candyNames = (foldr ((<|>) . try . string) mzero $ Data.List.map (upcase . unItem) candy) <?> "candy"

-- Extract the candy name from the Item wrapper
unItem :: (Item,Number) -> Name
unItem (Item a, b) = a


-- The initial state of the Vending machine
testMachine :: STM (TVar (Inventory, Change))
testMachine = newTVar (candy, [(Nickel, 1), (Quarter, 0), (Dime, 1), (Dollar, 1)])

candy = [(Item "SixtyFive"  ,10),
         (Item "Dollar"     , 1),
         (Item "BuckFifty", 9)]

-- Entry point into the program
main = server $ PortNumber 8000
