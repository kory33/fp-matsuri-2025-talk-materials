from enum import Enum
from manim import *
from typing import Callable, TypeAlias, TypeVar, Tuple, NamedTuple

# Vibe-coded with o4-mini-high and then edited
# https://chatgpt.com/share/6849cb15-b9c4-8000-9c96-2a8db0c9b9ae

class BinTreeDirection(Enum):
    LEFT = 1
    RIGHT = 2

A = TypeVar("A")
B = TypeVar("B")

TreeLike: TypeAlias = dict[Tuple[BinTreeDirection, ...], A]

def zip_with_children_from_root(tree: TreeLike[A]) -> TreeLike[Tuple[A, dict[BinTreeDirection, A]]]:
    result: TreeLike[Tuple[A, dict[BinTreeDirection, A]]] = {}
    
    for path, node_value in tree.items():
        children = {}
        for direction in BinTreeDirection:
            child_path = path + (direction,)
            if child_path in tree:
                children[direction] = tree[child_path]
        result[path] = (node_value, children)
    
    return result

def subtree_rooted_at_node_by_path(tree: TreeLike[A], path: Tuple[BinTreeDirection, ...]) -> TreeLike[A]:
    subtree: TreeLike[A] = {}
    for sub_path, node_value in tree.items():
        if sub_path[:len(path)] == path:
            subtree[sub_path[len(path):]] = node_value
    return subtree

def replace_subtree_with_tree(tree: TreeLike[A], target_path: Tuple[BinTreeDirection, ...], new_sub_tree: TreeLike[A]) -> TreeLike[A]:
    if target_path in tree:
        new_tree = {}
        for path, old_value in tree.items():
            if path[:len(path)] != target_path:
                new_tree[path] = old_value
        for sub_path, new_value in new_sub_tree.items():
            new_tree[target_path + sub_path] = new_value
        return new_tree
    else:
        return tree

class FoldExpressionTree_3625(Scene):
    background_color = WHITE

    def construct(self):
        # ─── Config ────────────────────────────────────────────────────────────
        LINE_WIDTH = 4
        BUFF      = 0.3   # extra padding around each symbol’s circle

        SLEEP_AFTER_REDEX_IDENTIFICATION = 0.3
        SLEEP_BETWEEN_REDUCTION_STEPS = 0.5

        NODE_CONFIG = dict(font_size=60, color=BLACK)
        LINE_CONFIG = dict(stroke_width=LINE_WIDTH, color=BLACK)

        self.camera.background_color = WHITE

        # ─── 1.0) Define data
        class ExprNode(NamedTuple):
            path: Tuple[BinTreeDirection, ...]
            node_value: MathTex

        root        = ExprNode((), MathTex("+", **NODE_CONFIG).move_to(UP * 2))
        left_plus   = ExprNode((BinTreeDirection.LEFT,), MathTex("+", **NODE_CONFIG).move_to(LEFT * 2))
        right_times = ExprNode((BinTreeDirection.RIGHT,), MathTex("\\times", **NODE_CONFIG).move_to(RIGHT * 2))
        leaf3       = ExprNode((BinTreeDirection.LEFT, BinTreeDirection.LEFT), MathTex("3", **NODE_CONFIG).move_to(LEFT * 3 + DOWN * 2))
        leaf6       = ExprNode((BinTreeDirection.LEFT, BinTreeDirection.RIGHT), MathTex("6", **NODE_CONFIG).move_to(LEFT * 1 + DOWN * 2))
        leaf2       = ExprNode((BinTreeDirection.RIGHT, BinTreeDirection.LEFT), MathTex("2", **NODE_CONFIG).move_to(RIGHT * 1 + DOWN * 2))
        leaf5       = ExprNode((BinTreeDirection.RIGHT, BinTreeDirection.RIGHT), MathTex("5", **NODE_CONFIG).move_to(RIGHT * 3 + DOWN * 2))

        tree: TreeLike[MathTex] = dict([(n.path, n.node_value) for n in [root, left_plus, right_times, leaf3, leaf6, leaf2, leaf5]])
        tree_nodes_group = VGroup(*tree.values())
        tree_nodes_group.to_edge(LEFT, buff=1)

        # ─── 1.1) “Circle‐aware” connector ────────────────────────────────────────
        def connect(parent: Mobject, child: Mobject) -> Line:
            p_center = parent.get_center()
            c_center = child.get_center()
            vec      = c_center - p_center
            direction = vec / np.linalg.norm(vec)
            # radius = half the bigger dimension + small BUFF
            r_p = max(parent.width,  parent.height) / 2 + BUFF
            r_c = max(child.width,   child.height)  / 2 + BUFF
            start = p_center + direction * r_p
            end   = c_center - direction * r_c
            return Line(start, end, **LINE_CONFIG)

        # ─── 1.2) generate edge cache ─────────────────────────────────────────────

        edge_from_parent: TreeLike[Line | None] = dict(
            [(path_to_parent + (direction,), connect(parent, child))
                for path_to_parent, (parent, children) in zip_with_children_from_root(tree).items()
                for direction, child in children.items()
            ] + [((), None)] # root has no parent
        )

        # ─── 1.3) define reduction step animation ─────────────────────────────────

        def animate_reduction(
            current_expr_tree: TreeLike[MathTex],
            current_expr: MathTex,
            current_expr_modification: Callable[[MathTex], MathTex],
            path_to_redex: Tuple[BinTreeDirection, ...],
            # Hack: We *hard-swap* current_expr with current_expr_body_double right before the transition effect
            #       because current_expr may not be split into suitable parts that allows matching by redex_part_in_expr.
            #       The rendering result of current_expr and current_expr_body_double must be the same, hence the name current_expr_body_double.
            current_expr_body_double: MathTex,
            redex_part_in_expr: str,
            new_expr_parts: Tuple[str, ...],
            # new_value must appear in new_expr_parts
            new_value: str,
            new_expr_right_edge_buff: float,
        ) -> tuple[TreeLike[MathTex], MathTex, Callable[[MathTex], MathTex]]:
            def vgroup_containing_direct_children_along_with_node_at(path: Tuple[BinTreeDirection, ...]) -> VGroup:
                nodes = [n for n in
                            [current_expr_tree.get(path), 
                            current_expr_tree.get(path + (BinTreeDirection.LEFT,)),
                            current_expr_tree.get(path + (BinTreeDirection.RIGHT,))]
                            if n is not None]
                edges = [e for e in
                            [edge_from_parent.get(path + (BinTreeDirection.LEFT,)),
                            edge_from_parent.get(path + (BinTreeDirection.RIGHT,))]
                            if e is not None]
                return VGroup(*nodes, *edges)

            modified_body_double = current_expr_modification(current_expr_body_double)
            self.remove(current_expr); self.add(modified_body_double) # *hard-swap*

            subtree = vgroup_containing_direct_children_along_with_node_at(path_to_redex)
            subtree_box = SurroundingRectangle(subtree, color=ORANGE, buff=0.3)
            subtree_expr_box = SurroundingRectangle(modified_body_double.get_part_by_tex(redex_part_in_expr), color=ORANGE, buff=0.1)

            self.play(Create(subtree_box), Create(subtree_expr_box))
            self.wait(SLEEP_AFTER_REDEX_IDENTIFICATION)

            new_value_node = MathTex(new_value, **NODE_CONFIG).move_to(current_expr_tree.get(path_to_redex).get_center())
            new_value_box = SurroundingRectangle(new_value_node, color=ORANGE, buff=0.1)

            new_expr_modification = lambda expr: expr.scale(0.8).to_edge(RIGHT, buff=new_expr_right_edge_buff)
            new_expr = new_expr_modification(MathTex(*new_expr_parts, arg_separator="", **NODE_CONFIG))
            new_expr_box = SurroundingRectangle(new_expr.get_part_by_tex(new_value), color=ORANGE, buff=0.1)

            self.play(
                ReplacementTransform(subtree, new_value_node),
                ReplacementTransform(subtree_box, new_value_box),
                ReplacementTransform(modified_body_double, new_expr),
                ReplacementTransform(subtree_expr_box, new_expr_box),
                run_time=0.6
            )
            self.play(FadeOut(new_value_box), FadeOut(new_expr_box), run_time=SLEEP_BETWEEN_REDUCTION_STEPS / 2)
            self.wait(SLEEP_BETWEEN_REDUCTION_STEPS / 2)

            return (replace_subtree_with_tree(current_expr_tree, path_to_redex, {(): new_value_node}), new_expr, new_expr_modification)

        # ─── 1.4) Prepare state variables ────────────────────────────────────────
        edges = VGroup(*[edge for edge in edge_from_parent.values() if edge is not None])
        current_expr_modification = lambda expr: expr.scale(0.8).to_edge(RIGHT, buff=1)
        expr = current_expr_modification(MathTex("(3+6)+(2\\times5)", arg_separator="", **NODE_CONFIG))

        # ─── 2.0) Start main animation ───────────────────────────────────────────
        self.wait(0.3)
        self.play(Create(VGroup(*tree.values()), lag_ratio=0))
        self.play(Create(VGroup(edges, expr), lag_ratio=0))

        # (3+6)+(2×5) → 9 +(2×5)
        tree, expr, current_expr_modification = animate_reduction(
            current_expr_tree=tree,
            current_expr=expr,
            current_expr_modification=current_expr_modification,
            path_to_redex=left_plus.path,
            current_expr_body_double=MathTex("(3+6)", "+(2\\times5)", **NODE_CONFIG),
            redex_part_in_expr="(3+6)",
            new_expr_parts=("9", "+(2\\times5)"),
            new_value="9",
            new_expr_right_edge_buff=2
        )

        # 9 + (2×5) → 9 + 10
        tree, expr, current_expr_modification = animate_reduction(
            current_expr_tree=tree,
            current_expr=expr,
            current_expr_modification=current_expr_modification,
            path_to_redex=right_times.path,
            current_expr_body_double=MathTex("9+", "(2\\times5)", **NODE_CONFIG),
            redex_part_in_expr="(2\\times5)",
            new_expr_parts=("9+", "10"),
            new_value="10",
            new_expr_right_edge_buff=3
        )

        # 9 + 10 → 19
        tree, expr, current_expr_modification = animate_reduction(
            current_expr_tree=tree,
            current_expr=expr,
            current_expr_modification=current_expr_modification,
            path_to_redex=root.path,
            current_expr_body_double=MathTex("9+10", **NODE_CONFIG),
            redex_part_in_expr="9+10",
            new_expr_parts=("19",),
            new_value="19",
            new_expr_right_edge_buff=3
        )
