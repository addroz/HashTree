module HashTree where

import Hashable32

data Tree a = Leaf {element :: a, nodeHash :: Hash} |
              Branch1 {subTree :: Tree a, nodeHash :: Hash} |
              Branch2 {subTree1 :: Tree a, subTree2 :: Tree a, nodeHash :: Hash}
              deriving (Show)

leaf :: Hashable a => a -> Tree a
node :: Hashable a => Tree a -> Tree a -> Tree a
twig :: Hashable a => Tree a -> Tree a
buildTree :: Hashable a => [a] -> Tree a
treeHash :: Tree a -> Hash
drawTree :: Show a => Tree a -> String

treeHash = nodeHash
leaf element = Leaf element (hash element)
twig tree = Branch1 tree (combine (treeHash tree) (treeHash tree))
node tree1 tree2 = Branch2 tree1 tree2 (combine (treeHash tree1) (treeHash tree2))

buildTreeFirstLevel :: Hashable a => [a] -> [Tree a]
buildTreeFirstLevel [element] = [twig (leaf element)]
buildTreeFirstLevel [element1, element2] = [node (leaf element1) (leaf element2)]
buildTreeFirstLevel (element1:element2:t) = buildTreeFirstLevel [element1, element2] ++ buildTreeFirstLevel t

buildTreeNextLevels :: Hashable a => [Tree a] -> [Tree a] -> Tree a
buildTreeNextLevels [tree] [] = tree
buildTreeNextLevels [] list = buildTreeNextLevels list []
buildTreeNextLevels [tree] list = buildTreeNextLevels [] (list ++ [twig tree])
buildTreeNextLevels (tree1:tree2:t) list = buildTreeNextLevels t (list ++ [node tree1 tree2])

buildTree [] = errorWithoutStackTrace "empty list"
buildTree [element] = leaf element
buildTree list = buildTreeNextLevels (buildTreeFirstLevel list) []

printWhitespaces :: Int -> String
printWhitespaces n = concat $ replicate n " "

drawTreeBegin :: Show a => Int -> Tree a -> String
drawTreeBegin n (Leaf element nodeHash) = concat [printWhitespaces (2*n), showHash nodeHash, " ", show element, "\n"]
drawTreeBegin n (Branch1 subtree nodeHash) = concat [printWhitespaces (2*n), showHash nodeHash, " +\n",
  drawTreeBegin (n+1) subtree]
drawTreeBegin n (Branch2 subtree1 subtree2 nodeHash) = concat [printWhitespaces (2*n), showHash nodeHash, " -\n",
  drawTreeBegin (n+1) subtree1, drawTreeBegin (n+1) subtree2]

drawTree = drawTreeBegin 0

type MerklePath = [Either Hash Hash]
data MerkleProof a = MerkleProof a MerklePath

buildProof :: Hashable a => a -> Tree a -> Maybe (MerkleProof a)
merklePaths :: Hashable a => a -> Tree a -> [MerklePath]
showMerklePath :: MerklePath -> String

merklePaths x (Leaf element nodeHash) | hash x == nodeHash = [[]]
                                      | otherwise = []

merklePaths x (Branch1 subtree nodeHash) = map ([Left (treeHash subtree)] ++) (merklePaths x subtree)

merklePaths x (Branch2 subtree1 subtree2 nodeHash) = map ([Left (treeHash subtree2)] ++) (merklePaths x subtree1)
                                                     ++ map ([Right (treeHash subtree1)] ++) (merklePaths x subtree2)

buildProof a t | null (merklePaths a t) = Nothing
               | otherwise = Just (MerkleProof a (head (merklePaths a t)))

showMerklePath [] = ""
showMerklePath (Left h:t) = "<" ++ showHash h ++ showMerklePath t
showMerklePath (Right h:t) = ">" ++ showHash h ++ showMerklePath t

instance Show a => Show (MerkleProof a) where
  showsPrec p (MerkleProof element path) = showParen(p>10)(("MerkleProof " ++).showsPrec 11 element.(" " ++).(showMerklePath path ++))

verifyProof :: Hashable a => Hash -> MerkleProof a -> Bool
getTreeHash :: Hashable a => a -> MerklePath -> Hash

getTreeHash x [] = hash x
getTreeHash x (Left y:t) = combine (getTreeHash x t) y
getTreeHash x (Right y:t) = combine y (getTreeHash x t)

verifyProof hash (MerkleProof element path) = (getTreeHash element path) == hash

{- | Tree drawing
>>> putStr $ drawTree $ buildTree "fubar"
0x2e1cc0e4 -
  0xfbfe18ac -
    0x6600a107 -
      0x00000066 'f'
      0x00000075 'u'
    0x62009aa7 -
      0x00000062 'b'
      0x00000061 'a'
  0xd11bea20 +
    0x7200b3e8 +
      0x00000072 'r'
-}

{- | Paths & Proofs
>>> mapM_ print $ map showMerklePath  $ merklePaths 'i' $ buildTree "bitcoin"
"<0x5214666a<0x7400b6ff>0x00000062"
">0x69f4387c<0x6e00ad98>0x0000006f"

>>> buildProof 'i' $ buildTree "bitcoin"
Just (MerkleProof 'i' <0x5214666a<0x7400b6ff>0x00000062)

>>> buildProof 'e' $ buildTree "bitcoin"
Nothing
-}

{- | Proof verification
>>> let t = buildTree "bitcoin"
>>> let proof = buildProof 'i' t
>>> verifyProof (treeHash t) <$> proof
Just True
>>> verifyProof 0xbada55bb <$> proof
Just False
-}

{- | Testy ze slacka
>>> merklePaths 'i' $ buildTree "bitcoin"
[[Left 1377068650,Left 1946203903,Right 98],[Right 1777612924,Left 1845538200,Right 111]]

>>> putStr $ drawTree $ buildTree ""
*** Exception: empty list

>>> buildProof 'a' $ buildTree "a"
Just (MerkleProof 'a' )

-}

{- | Some custom edge-cases tests
>>> putStr $ drawTree $ buildTree "a"
0x00000061 'a'

>>> putStr $ drawTree $ buildTree "ab"
0x61009915 -
  0x00000061 'a'
  0x00000062 'b'

>>> merklePaths 'i' $ buildTree "i"
[[]]

>>> merklePaths 'a' $ buildTree "i"
[]
-}