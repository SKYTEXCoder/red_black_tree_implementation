use red_black_tree_implementation::rbtree_implementation::RedBlackTree;

fn main() {
    let mut tree: RedBlackTree = RedBlackTree::new();
    let keys: [i32; 32] = [
        14, 90, 15, 30, 20, 25, 10, 5, 4, 3, 2, 1, 7, 11, 86, 99, 19, 27, 24, 22, 47, 61, 56, 16, 17, 18,
        21, 23, 26, 28, 29, 31,
    ];
    for key in keys.iter() {
        println!("Inserting key: {}", key);
        tree.insert(*key);
        tree.print_tree("inorder");
    }
    tree.print_tree("inorder");
    println!("Searching for node with key 7...");
    if let Some(node_to_delete) = tree.search(7) {
        println!("Deleting node with key 7...");
        tree.delete(node_to_delete);
        tree.print_tree("inorder");
    } else {
        println!("Node with key 7 not found.");
    }

    println!("Searching for node with key 11...");
    if let Some(node_to_delete) = tree.search(11) {
        println!("Deleting node with key 11...");
        tree.delete(node_to_delete);
        tree.print_tree("inorder");
    } else {
        println!("Node with key 11 not found.");
    }

    tree.pretty_print_tree();
}
