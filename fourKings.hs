{-# LANGUAGE PackageImports, Rank2Types, DeriveFunctor #-}
import Haste
import Data.List
import Data.Maybe (fromJust)
import Data.Default
import qualified Data.Foldable as F
import "mtl" Control.Monad.State
import Data.IORef
import qualified Data.Sequence as S

foreign import ccall jsSetInnerText :: Elem -> JSString -> IO ()
setInnerText :: Elem -> String -> IO ()
setInnerText em = jsSetInnerText em . toJSString

newParagraph :: String -> IO Elem
newParagraph s = do
  p <- newElem "p"
  setInnerText p s
  return p

addAttr :: (MonadIO m) => Elem -> PropID -> String -> m ()
addAttr e p s = do
  s' <- getAttr e p
  setAttr e p $ s' ++ " " ++ s

type Lens s t a b = Functor f => (a -> f b) -> s -> f t
type Lens' s a = Lens s s a a

lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens sa sbt afb s = sbt s `fmap` afb (sa s)
newtype Identity a = Identity { runIdentity :: a } deriving (Functor)
newtype Const a b = Const { getConst :: a } deriving (Functor)

(^.) :: s -> Lens' s a -> a
s ^. l = getConst $ l Const s

(.~) :: Lens s t a b -> b -> s -> t
l .~ b = runIdentity . l (\_ -> Identity b)

(%~) :: Lens s t a b -> (a -> b) -> s -> t
l %~ f = runIdentity . l (Identity . f)

infixl 5 &
(&) :: a -> (a -> b) -> b
(&) = flip ($)

data Suit = Spade | Hart | Diamond | Club deriving (Eq, Ord, Enum)
instance Show Suit where
  show Spade = "♠"
  show Hart = "♥"
  show Diamond = "♦"
  show Club = "♣"
data Card = Card Suit Int | Joker Int | Back deriving (Eq)

allCards :: [Card]
allCards = [Card s n | s <- [Spade .. Club], n <- [1..13]] ++ [Joker 0, Joker 0]

cardOrder :: [Int]
cardOrder = [3,4,5,6,7,8,9,10,11,12,13,1,2,0]

(<:=) :: Int -> Int -> Bool
(<:=) n m = (fromJust $ n `elemIndex` cardOrder)
         <= (fromJust $ m `elemIndex` cardOrder)

(<:) :: Int -> Int -> Bool
(<:) n m = (fromJust $ n `elemIndex` cardOrder)
         < (fromJust $ m `elemIndex` cardOrder)

cardNumber :: Card -> Int
cardNumber (Card _ n) = n
cardNumber (Joker _) = 0
cardNumber Back = -1

cardImg :: Card -> IO Elem
cardImg c = do
  sp <- newElem "a"
  setAttr sp "class" "card"
  setStyle sp "background-position" $
    (\(x,y) -> "-" ++ show x ++ "px " ++ "-" ++ show y ++ "px") $ offset c
  setProp sp "style" $ 
    "background-position: " ++ 
      ((\(x,y) -> "-" ++ show x ++ "px " ++ "-" ++ show y ++ "px;") $ offset c)
  return sp
  
  where
    suit :: Suit -> Int
    suit s = 60*(fromJust $ s `elemIndex` [Hart, Spade, Diamond, Club])
    
    offset :: Card -> (Int, Int)
    offset (Card s n) = (suit s, 90*(n-1))
    offset (Joker 0) = (0, 1170)
    offset (Joker _) = (60, 1170)
    offset Back = (180, 1170)

instance Show Card where
  show (Card s 1) = show s ++ "A"
  show (Card s 11) = show s ++ "J"
  show (Card s 12) = show s ++ "Q"
  show (Card s 13) = show s ++ "K"
  show (Card s n) = show s ++ show n
  show (Joker n)
    | n == 0 = "Joker"
    | otherwise = "Joker " ++ show n
  show Back = "＊"
instance Ord Card where
  _ <= Joker _ = True
  Joker _ <= _ = False
  (Card s m) <= (Card t n)
    | m == n = s <= t
    | otherwise = m <:= n
  _ <= _ = True

data Action = None | Pass | Discard [Card] | Declare Card deriving (Eq, Show)
data Player = Player {
  _hands :: [Card],
  _gained :: [Card],
  _scores :: [Int]
  } deriving (Show)

data BState = Init | Dealing | Waiting Int | GameOver deriving (Eq, Show)
fromWaiting :: BState -> Int
fromWaiting (Waiting n) = n
fromWaiting _ = undefined

isWaiting :: BState -> Bool
isWaiting (Waiting _) = True
isWaiting _ = False

data Board = Board {
  _players :: S.Seq Player,
  _king :: Int,
  _playing :: BState,
  _talons :: [Card],
  _layouts :: [(Int, [Card])],
  _deck :: [Card],
  _turn :: Int,
  _special :: [Card],
  _actHistory :: [Action]
  }

instance Default Player where def = Player [] [] []
instance Default Board where
  def = Board (S.fromList [def, def, def, def]) 0 GameOver allCards [] [] 0 [] []

hands :: Lens' Player [Card]; hands = lens _hands (\p x -> p { _hands = x })
gained :: Lens' Player [Card]; gained = lens _gained (\p x -> p { _gained = x })
scores :: Lens' Player [Int]; scores = lens _scores (\p x -> p { _scores = x })

players :: Lens' Board (S.Seq Player); players = lens _players (\p x -> p { _players = x })
king :: Lens' Board Int; king = lens _king (\p x -> p { _king = x })
playing :: Lens' Board BState; playing = lens _playing (\p x -> p { _playing = x })
talons :: Lens' Board [Card]; talons = lens _talons (\p x -> p { _talons = x })
layouts :: Lens' Board [(Int, [Card])]; layouts = lens _layouts (\p x -> p { _layouts = x })
deck :: Lens' Board [Card]; deck = lens _deck (\p x -> p { _deck = x })
turn :: Lens' Board Int; turn = lens _turn (\p x -> p { _turn = x })
special :: Lens' Board [Card]; special = lens _special (\p x -> p { _special = x })
actHistory :: Lens' Board [Action]; actHistory = lens _actHistory (\p x -> p { _actHistory = x })

which :: (Card, Int) -> [Card] -> [[Card]]
which (c,n) cs
  | n == 0 = groupBy eq' $ sort cs
  | otherwise =
  [take n x | x <- groupBy eq' $ sort cs, length x >= n,
              cardNumber c <: cardNumber (x !! 0)]
  where
    eq' (Card _ n) (Card _ m) = n == m
    eq' _ _ = False

whichWithOne :: (Card, Int) -> [Card] -> [[Card]]
whichWithOne k cs = sort $ 
  [[x]| x <- cs, not $ x `elem` (concat $ which k cs)] ++ which k cs

runAction :: Int -> Action -> Board -> Board
runAction _ None b = b
runAction n Pass b = b
  & turn %~ (+1)
  & playing .~ Waiting ((n+1) `mod` 4)
  & actHistory %~ (Pass :)
runAction n (Discard cs) b = b
  & turn %~ (+1)
  & playing .~ Waiting ((n+1) `mod` 4)
  & layouts %~ (++ [(fromWaiting $ b^.playing, cs)])
  & players %~ S.adjust (hands %~ delAllFrom cs) n
  & deck .~ cs
  & actHistory %~ (Discard cs :)
runAction n (Declare c) b = b
  & players %~ S.adjust (hands %~ delete c) 0
  & special %~ (c:)

delAllFrom :: [Card] -> [Card] -> [Card]
delAllFrom (c:cs) h = delAllFrom cs $ delete c h
delAllFrom [] h = h

strategy :: [Card] -> Player -> Action
strategy d p = let d' = (d !! 0, length $ d) in
  case which d' (p^.hands) of
  [] -> Pass
  p -> Discard $ p !! 0

clearLayouts :: IORef Board -> IO ()
clearLayouts b = do
  s <- readIORef b
  let n = fromWaiting $ s^.playing
  writeIORef b $ s
    & layouts .~ []
    & deck .~ []
    & players %~ S.adjust (gained %~ ((concat $ fmap snd $ s^.layouts) ++)) n

gameover :: IORef Board -> IO ()
gameover b = do
  s <- readIORef b
  let pairs = F.toList $ cardScore $ s^.special
  writeIORef b $ s
    & players %~ fmap (\p -> p & scores %~ (++ 
      [sum $ map (\x -> fromJust $ lookup (cardNumber x) pairs) $ p^.gained]))
    & playing .~ GameOver
  
  where
    point :: Int -> Int
    point 13 = -10
    point n = n
  
    multiplier :: Int -> Int
    multiplier 0 = 40
    multiplier 1 = 30
    multiplier 2 = 20
    multiplier 3 = 15
    multiplier _ = 0

    cardScore :: [Card] -> S.Seq (Int, Int)
    cardScore (c:cs) = S.update (cardNumber c)
      (cardNumber c, multiplier $ length cs) $ cardScore cs
    cardScore [] = S.fromList [(n, point n) | n <- [0..13]]

gameinit :: IORef Board -> IO ()
gameinit b = do
  s <- readIORef b
  writeIORef b $ s
    & players %~ fmap (\p -> p & hands .~ [] & gained .~ [])
    & playing .~ Init
    & layouts .~ []
    & deck .~ []
    & talons .~ allCards
    & turn .~ 1
    & special .~ []

updateBoard :: IORef Board -> IO ()
updateBoard b = do
  s <- readIORef b
  case s^.playing of
    Init -> do
      t' <- shuffle $ s^.talons
      writeIORef b $ s & playing .~ Dealing & talons .~ t'
    Dealing -> do
      u <- deal $ s
      let i = searchSpadeK (u^.players)
      writeIORef b $ u
        & king .~ i
        & playing .~ Waiting i
    _ -> return ()

  s <- readIORef b
  when (isWaiting (s^.playing) &&
       ((== [Pass, Pass, Pass]) $ take 3 $ s^.actHistory)) $
    clearLayouts b
  when (isWaiting (s^.playing) && (s^.actHistory) /= []) $ do
    case head $ s^.actHistory of
      Discard cs -> when ((== 8) $ cardNumber $ head cs) $ do
        writeIORef b $ s & playing %~ (\(Waiting n) -> Waiting $ (n+3) `mod` 4)
        clearLayouts b
      _ -> return ()
  when (isWaiting (s^.playing) &&
       ((/= 0) . S.length . S.filter ((== 0) . length) . fmap (^.hands) $ s^.players)) $
    gameover b

  where
    searchSpadeK :: S.Seq Player -> Int
    searchSpadeK ps = 
      case S.elemIndexL True . fmap (\p -> Card Spade 13 `elem` (p^.hands)) $ ps of
        Just n -> n
        Nothing -> 0
  
    deal :: Board -> IO Board
    deal b = do
      let ps = _players b
      cs <- shuffle $ b^.talons
      let css = zip [0..] . slice (length cs `div` S.length ps + 1) $ cs
      return $ b
        & talons .~ []
        & players .~ foldl
            (\p' (n,cs) -> S.update n ((p' `S.index` n) & hands .~ cs) p') ps css
    
    shuffle :: [a] -> IO [a]
    shuffle cs = do
      s <- newSeed
      return $ shuffle' s cs []

    shuffle' :: Seed -> [a] -> [a] -> [a]
    shuffle' _ [] acc = acc
    shuffle' _ [x] acc = acc ++ [x]
    shuffle' s l acc =
      let (k, s') = randomR (0, length l-1) s;
          (lead, x:xs) = splitAt k l in
      shuffle' s' (lead ++ xs) (x:acc)

    slice :: Int -> [a] -> [[a]]
    slice n = unfoldr phi where
      phi [] = Nothing
      phi xs = Just $ splitAt n xs

scoreTable :: Board -> Elem -> IO ()
scoreTable b em = do
  table <- newElem "table"
  addChild table em
  c <- newElem "caption"
  setInnerText c "対戦成績"
  addChild c table
  
  tr <- newElem "tr"
  addChild tr table
  flip mapM_ [0..S.length (b^.players)-1] $ \i -> do
    th <- newElem "th"
    setInnerText th $ if i == 0 then "自分" else "Player " ++ show i
    addChild th tr

  flip mapM_ [0..length (b^.players `S.index` 0^.scores)-1] $ \i -> do
    tr' <- newElem "tr"
    addChild tr' table
    flip mapM_ [0..S.length (b^.players)-1] $ \j -> do
      td <- newElem "td"
      setInnerText td $ show $ b^.players `S.index` j^.scores !! i
      addChild td tr'

drawBoard :: IORef Board -> IO ()
drawBoard b = do
  k <- readIORef b
  Just h <- elemById "header"
  clearChildren h
  p1 <- newParagraph $ if k^.playing /= GameOver then "ゲーム開始！" else "ゲーム終了！"
  p2 <- newParagraph $ (show $ length (k^.players `S.index` 0^.scores)+1) ++ "試合目/" ++ (show $ (k^.turn+1) `div` 4) ++ "ターン"
  addChild p1 h
  addChild p2 h
  
  Just oh <- elemById "otherhands"
  clearChildren oh
  flip mapM_ [1..S.length (k^.players)-1] $ \i -> do
    pDiv <- newElem "div"
    addChild pDiv oh
    setAttr pDiv "class" $ "player-" ++ show i

    pa <- newParagraph $ "Player " ++ show i ++ ":"
    when (Waiting i == k^.playing) $ do
      addAttr pDiv "class" "now"
    addChild pa pDiv
    
    handsDiv <- newElem "div"
    addChild handsDiv pDiv
    setAttr handsDiv "class" "hands"
    forM_ (k^.players `S.index` i^.hands) $ \_ -> do
      c <- cardImg Back
      addChild c handsDiv
    gainedDiv <- newElem "div"
    addChild gainedDiv pDiv
    setAttr gainedDiv "class" "gained"
    forM_ (k^.players `S.index` i^.gained) $ \j -> do
      c <- cardImg j
      addChild c gainedDiv

  Just l <- elemById "layouts"
  clearChildren l
  lDiv <- newElem "div"
  setAttr lDiv "class" "layouted"
  addChild lDiv l
  p <- newParagraph "場に出ている札:"
  addChild p lDiv
  forM_ (k^.layouts) $ \(i,cs) -> do
    forM_ cs $ \j -> do
      c <- cardImg j
      addChild c lDiv
      addAttr c "class" $ "player-" ++ show i

  dDiv <- newElem "div"
  setAttr dDiv "class" "declared"
  addChild dDiv l
  p' <- newParagraph $ "宣言された札:"
  addChild p' dDiv
  forM_ (k^.special) $ \i -> do
    c <- cardImg i
    addChild c dDiv

  Just t <- elemById "table"
  clearChildren t
  scoreTable k t
  case (k^.playing == GameOver) of
    True -> do
      setStyle t "display" "block"
      setProp t "style" "display: block;"
    False -> do
      setStyle t "display" "none"
      setProp t "style" "display: none;"
 
mkButton :: IORef Board -> Elem -> Card -> [Card] -> IO ()
mkButton b em c pair = do
  k <- readIORef b
  addAttr em "class" $ "button-" ++ show (cardNumber c)

  k <- readIORef b
  em `onEvent` OnClick $ \_ _ -> do
    writeIORef b $ (runAction 0 (Discard pair) k)
    setTimeout 150 $ runLoop b
  return ()

decButton :: IORef Board -> Card -> Elem -> IO ()
decButton b c em = do
  t <- newElem "button"
  addChild t em
  setInnerText t $ show c
  setStyle t "margin-left" "5px"
  setStyle t "font-size" "18px"

  k <- readIORef b
  t `onEvent` OnClick $ \_ _ -> do
    writeIORef b $ (runAction 0 (Declare c)) k
    setTimeout 150 $ runLoop b
  return ()

passButton :: IORef Board -> Elem -> Bool -> IO ()
passButton b h isEnabled = do
  pass <- newElem "button"
  setAttr pass "class" "ball"
  setInnerText pass "パス"
  addChild pass h
  when (not isEnabled) $ do
    setAttr pass "disabled" "disabled"

  k <- readIORef b
  pass `onEvent` OnClick $ \_ _ -> do
    writeIORef b $ (runAction 0 Pass) k
    setTimeout 150 $ runLoop b
  return ()

playerTurn :: IORef Board -> IO ()
playerTurn b = do
  k <- readIORef b
  let d = (k^.deck !! 0, length $ k^. deck)
  let myCards = sort $ (k^.players `S.index` 0)^.hands

  Just h <- elemById "hands"
  when (Waiting 0 == k^.playing) $ do
    setAttr h "class" "now"
  clearChildren h
  p <- newParagraph $ "手札:"
  addChild p h
  
  handsDiv <- newElem "div"
  setAttr handsDiv "class" "hands"
  addChild handsDiv h
  when (k^.playing /= Waiting 0) $ do
    passButton b handsDiv False
    forM_ myCards $ \i -> do
      c <- cardImg i
      addChild c handsDiv
  case k^.playing of
    Waiting 0 -> do
      passButton b handsDiv True
      forM_ (whichWithOne d myCards) $ \i -> do
        sp <- newElem "span"
        setAttr sp "class" "cards"
        addChild sp handsDiv
        forM_ i $ \j -> do
          c <- cardImg j
          addChild c sp
          when (i `elem` which d myCards) $ do
            mkButton b c j i
    GameOver -> do
      Just n <- elemById "newGame"
      t <- newElem "button"
      setAttr t "class" "ball"
      addChild t n
      setInnerText t $ "ニューゲーム"

      t `onEvent` OnClick $ \_ _ -> do
        clearChildren n
        gameinit b
        setTimeout 150 $ runLoop b
      return ()
    _ -> return ()

  gainedDiv <- newElem "div"
  setAttr gainedDiv "class" "gained"
  addChild gainedDiv h
  forM_ (k^.players `S.index` 0^.gained) $ \i -> do
    c <- cardImg i
    addChild c gainedDiv

  k <- readIORef b
  dDiv <- newElem "div"
  setAttr dDiv "class" "declared"
  addChild dDiv h
  when (k^.king == 0) $ do
    when (length (k^.special) < 4) $ do
      p <- newParagraph $ "カードを宣言:"
      addChild p dDiv
      when (not $ isWaiting $ k^.playing) $ setAttr p "disabled" "disabled"
      mapM_ (\x -> decButton b x dDiv) $ 
        filter (\s -> not $ cardNumber s `elem` fmap cardNumber (k^.special))
               (fmap head $ group $ sort $ myCards)

cpuTurn :: IORef Board -> IO ()
cpuTurn b = do
  s <- readIORef b
  case s^.playing of
    Waiting n -> writeIORef b $ 
      runAction n (strategy (s^.deck) (s^.players `S.index` n)) s
    _ -> return ()

runLoop :: IORef Board -> IO ()
runLoop b = do
  updateBoard b
  drawBoard b
  k <- readIORef b
  case (k^.playing == GameOver) || (k^.playing == Waiting 0) of
    True -> playerTurn b
    False -> cpuTurn b
  when ((k^.playing) /= Waiting 0 && (k^.playing) /= GameOver) $ do
    setTimeout 150 $ runLoop b

main :: IO ()
main = do
  b <- newIORef (def :: Board)
  runLoop b
