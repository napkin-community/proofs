inductive BinaryTree T where
| leaf (data : T)
| node (left right : BinaryTree T)

#check BinaryTree.node (BinaryTree.leaf 5) (BinaryTree.leaf 7)
#check BinaryTree.leaf 10
