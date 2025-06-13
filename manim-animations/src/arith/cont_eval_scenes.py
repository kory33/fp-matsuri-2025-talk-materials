from enum import Enum
from typing import (
    Any,
    Callable,
    Iterable,
    NamedTuple,
    Union,
    Tuple,
    Literal,
    TypedDict,
)

import numpy as np
from manim import (
    ManimColor,
    Mobject,
    Scene,
    VGroup,
    MathTex,
    Line,
    Create,
    SurroundingRectangle,
    ReplacementTransform,
    rate_functions,
    Succession,
    FadeOut,
    config,
    AnimationGroup,
    Star,
)
from manim.typing import Vector2D, Vector3D
from manim.utils.color.manim_colors import *
from manim.constants import *

config.max_files_cached = 1000


def connect(
    parent: Mobject, child: Mobject, BUFF: float, LINE_CONFIG: dict[str, Any]
) -> Line:
    p_center = parent.get_center()
    c_center = child.get_center()
    vec = c_center - p_center
    direction = vec / np.linalg.norm(vec)
    # radius = half the bigger dimension + small BUFF
    r_p = max(parent.width, parent.height) / 2 + BUFF
    r_c = max(child.width, child.height) / 2 + BUFF
    start = p_center + direction * r_p
    end = c_center - direction * r_c
    return Line(start, end, **LINE_CONFIG)


class AddArithExprWithNodePos(TypedDict):
    tag: Literal["aexpr-add"]
    left: "ArithExpr"
    right: "ArithExpr"
    symbol_pos: Vector2D


class MulArithExprWithNodePos(TypedDict):
    tag: Literal["aexpr-mul"]
    left: "ArithExpr"
    right: "ArithExpr"
    symbol_pos: Vector2D


class IntLitArithExprWithNodePos(TypedDict):
    tag: Literal["aexpr-int-lit"]
    value: int
    symbol_pos: Vector2D


ArithExpr = Union[
    AddArithExprWithNodePos, MulArithExprWithNodePos, IntLitArithExprWithNodePos
]


def ae_root_pos(expr: ArithExpr) -> Vector3D:
    return np.array((expr["symbol_pos"][0], expr["symbol_pos"][1], 0))


def vector2d_to_vector3d(v: Vector2D) -> Vector3D:
    return np.array((v[0], v[1], 0))


ChildDirection = Literal["left", "right"]
childDirections: Tuple[ChildDirection, ...] = ("left", "right")
childDirectionRight: ChildDirection = "right"
childDirectionLeft: ChildDirection = "left"
PathInExpr = Tuple[ChildDirection, ...]


def ae_zip_nodes_with_paths(
    expr: ArithExpr, prefix: PathInExpr = ()
) -> Iterable[Tuple[PathInExpr, ArithExpr]]:
    if expr["tag"] == "aexpr-int-lit":
        yield (prefix, expr)
    elif expr["tag"] == "aexpr-add":
        yield (prefix, expr)
        yield from ae_zip_nodes_with_paths(expr["left"], prefix + ("left",))
        yield from ae_zip_nodes_with_paths(expr["right"], prefix + ("right",))
    elif expr["tag"] == "aexpr-mul":
        yield (prefix, expr)
        yield from ae_zip_nodes_with_paths(expr["left"], prefix + ("left",))
        yield from ae_zip_nodes_with_paths(expr["right"], prefix + ("right",))


class ThenProceedToRightOfAddAEWithNodePos(TypedDict):
    tag: Literal["cont-then-proceed-to-right-of-add-ae"]
    right: ArithExpr
    symbol_pos: Vector2D
    placeholder_pos: Vector2D


class ThenAddLitFromLeftWithNodePos(TypedDict):
    tag: Literal["cont-then-add-lit-from-left"]
    left: int
    symbol_pos: Vector2D
    literal_pos: Vector2D
    placeholder_pos: Vector2D


class ThenProceedToRightOfMulAEWithNodePos(TypedDict):
    tag: Literal["cont-then-proceed-to-right-of-mul-ae"]
    right: ArithExpr
    symbol_pos: Vector2D
    placeholder_pos: Vector2D


class ThenMulLitFromLeftWithNodePos(TypedDict):
    tag: Literal["cont-then-mul-lit-from-left"]
    left: int
    symbol_pos: Vector2D
    literal_pos: Vector2D
    placeholder_pos: Vector2D


ArithCont = Union[
    ThenProceedToRightOfAddAEWithNodePos,
    ThenAddLitFromLeftWithNodePos,
    ThenProceedToRightOfMulAEWithNodePos,
    ThenMulLitFromLeftWithNodePos,
]


def ac_root_pos(cont: ArithCont) -> Vector3D:
    if (
        cont["tag"] == "cont-then-proceed-to-right-of-add-ae"
        or cont["tag"] == "cont-then-add-lit-from-left"
        or cont["tag"] == "cont-then-proceed-to-right-of-mul-ae"
        or cont["tag"] == "cont-then-mul-lit-from-left"
        or cont["tag"] == "cont-then-mul-lit-from-left"
    ):
        return np.array((cont["symbol_pos"][0], cont["symbol_pos"][1], 0))


MachineTrace = Tuple[Tuple[ArithExpr, Tuple[ArithCont, ...]], ...]


def trace_evaluation_of(expr_init: ArithExpr) -> MachineTrace:
    current_expr_of_interest: ArithExpr = expr_init
    current_continuation_stack: Tuple[ArithCont, ...] = ()
    trace: MachineTrace = ()
    while True:
        expr: ArithExpr = current_expr_of_interest
        cont_stack: Tuple[ArithCont, ...] = current_continuation_stack

        trace = trace + ((expr, cont_stack),)

        if expr["tag"] == "aexpr-int-lit":
            if not cont_stack:
                # no continuation left, we are done
                return trace
            else:
                lit: int = expr["value"]
                continuation: ArithCont = cont_stack[-1]
                new_stack: Tuple[ArithCont, ...] = cont_stack[:-1]
                if continuation["tag"] == "cont-then-proceed-to-right-of-add-ae":
                    current_expr_of_interest = continuation["right"]
                    current_continuation_stack = new_stack + (
                        {
                            "tag": "cont-then-add-lit-from-left",
                            "left": lit,
                            "symbol_pos": continuation["symbol_pos"],
                            "literal_pos": continuation["placeholder_pos"],
                            "placeholder_pos": continuation["right"]["symbol_pos"],
                        },
                    )
                elif continuation["tag"] == "cont-then-add-lit-from-left":
                    current_expr_of_interest = {
                        "tag": "aexpr-int-lit",
                        "value": lit + continuation["left"],
                        "symbol_pos": current_expr_of_interest["symbol_pos"],
                    }
                    current_continuation_stack = new_stack
                elif continuation["tag"] == "cont-then-proceed-to-right-of-mul-ae":
                    current_expr_of_interest = continuation["right"]
                    current_continuation_stack = new_stack + (
                        {
                            "tag": "cont-then-mul-lit-from-left",
                            "left": lit,
                            "symbol_pos": continuation["symbol_pos"],
                            "literal_pos": continuation["placeholder_pos"],
                            "placeholder_pos": continuation["right"]["symbol_pos"],
                        },
                    )
                elif continuation["tag"] == "cont-then-mul-lit-from-left":
                    current_expr_of_interest = {
                        "tag": "aexpr-int-lit",
                        "value": lit * continuation["left"],
                        "symbol_pos": current_expr_of_interest["symbol_pos"],
                    }
                    current_continuation_stack = new_stack
        else:
            if expr["tag"] == "aexpr-add":
                if expr["left"]["tag"] == "aexpr-int-lit":
                    current_expr_of_interest = expr["right"]
                    current_continuation_stack = cont_stack + (
                        {
                            "tag": "cont-then-add-lit-from-left",
                            "left": expr["left"]["value"],
                            "symbol_pos": expr["symbol_pos"],
                            "literal_pos": expr["left"]["symbol_pos"],
                            "placeholder_pos": expr["right"]["symbol_pos"],
                        },
                    )
                else:
                    current_expr_of_interest = expr["left"]
                    current_continuation_stack = cont_stack + (
                        {
                            "tag": "cont-then-proceed-to-right-of-add-ae",
                            "right": expr["right"],
                            "symbol_pos": expr["symbol_pos"],
                            "placeholder_pos": expr["left"]["symbol_pos"],
                        },
                    )
            elif expr["tag"] == "aexpr-mul":
                if expr["left"]["tag"] == "aexpr-int-lit":
                    current_expr_of_interest = expr["right"]
                    current_continuation_stack = cont_stack + (
                        {
                            "tag": "cont-then-mul-lit-from-left",
                            "left": expr["left"]["value"],
                            "symbol_pos": expr["symbol_pos"],
                            "literal_pos": expr["left"]["symbol_pos"],
                            "placeholder_pos": expr["right"]["symbol_pos"],
                        },
                    )
                else:
                    current_expr_of_interest = expr["left"]
                    current_continuation_stack = cont_stack + (
                        {
                            "tag": "cont-then-proceed-to-right-of-mul-ae",
                            "right": expr["right"],
                            "symbol_pos": expr["symbol_pos"],
                            "placeholder_pos": expr["left"]["symbol_pos"],
                        },
                    )


class EvalWithContinuation_Expression_13479(Scene):
    background_color = WHITE

    def construct(self):
        # ─── Config ────────────────────────────────────────────────────────────
        LINE_WIDTH = 4
        BUFF = 0.3  # extra padding around each symbol’s circle

        FOCUSED_SUBTREE_COLOR = ManimColor("#b5227f")
        POSTPONED_SUBTREE_COLOR = ManimColor("#007783")

        SLEEP_BETWEEN_EXPR_PATTERN_MATCH_STEPS = 0.4
        SLEEP_AFTER_REDEX_IDENTIFICATION = 0.15
        SUBTREE_DECOMPOSITION_ANIMATION_DURATION = 1.0

        NODE_CONFIG: dict[str, Any] = {"font_size": 60, "color": BLACK}
        LINE_CONFIG: dict[str, Any] = {"stroke_width": LINE_WIDTH, "color": BLACK}

        self.camera.background_color = WHITE

        trace = trace_evaluation_of(
            {
                "tag": "aexpr-add",
                "left": {
                    "tag": "aexpr-add",
                    "left": {
                        "tag": "aexpr-add",
                        "left": {
                            "tag": "aexpr-int-lit",
                            "value": 1,
                            "symbol_pos": np.array((-3.5, -1)),
                        },
                        "right": {
                            "tag": "aexpr-int-lit",
                            "value": 3,
                            "symbol_pos": np.array((-2, -1)),
                        },
                        "symbol_pos": np.array((-2.75, 1)),
                    },
                    "right": {
                        "tag": "aexpr-mul",
                        "left": {
                            "tag": "aexpr-int-lit",
                            "value": 4,
                            "symbol_pos": np.array((-0.5, -1)),
                        },
                        "right": {
                            "tag": "aexpr-int-lit",
                            "value": 7,
                            "symbol_pos": np.array((1, -1)),
                        },
                        "symbol_pos": np.array((0.25, 1)),
                    },
                    "symbol_pos": np.array((-1.25, 2)),
                },
                "right": {
                    "tag": "aexpr-int-lit",
                    "value": 9,
                    "symbol_pos": np.array((2, 2)),
                },
                "symbol_pos": np.array((0, 3)),
            }
        )

        def compile_arith_expr(
            expr: ArithExpr,
            decide_color_of_edge_reaching: Callable[
                [PathInExpr], ManimColor
            ] = lambda _: BLACK,
            decide_color_of_node: Callable[[PathInExpr], ManimColor] = lambda _: BLACK,
        ) -> Tuple[dict[PathInExpr, MathTex], dict[PathInExpr, Line]]:
            def symbol_for_root_of(expr: ArithExpr) -> str:
                if expr["tag"] == "aexpr-add":
                    return "+"
                elif expr["tag"] == "aexpr-mul":
                    return "\\times"
                elif expr["tag"] == "aexpr-int-lit":
                    return str(expr["value"])

            node_vobjs = dict(
                [
                    (
                        path,
                        MathTex(symbol_for_root_of(subexpr), **NODE_CONFIG)
                        .move_to(ae_root_pos(subexpr))
                        .set_color(decide_color_of_node(path)),
                    )
                    for path, subexpr in ae_zip_nodes_with_paths(expr)
                ]
            )
            edge_vobjs = dict(
                [
                    (
                        path + (direction,),
                        connect(
                            parent_vobj,
                            node_vobjs[path + (direction,)],
                            BUFF,
                            LINE_CONFIG,
                        ).set_color(decide_color_of_edge_reaching(path + (direction,))),
                    )
                    for path, parent_vobj in node_vobjs.items()
                    for direction in childDirections
                    if (path + (direction,) in node_vobjs)
                ]
            )

            return node_vobjs, edge_vobjs

        class ContinuationCompilationResult(NamedTuple):
            non_placeholder_nodes: dict[PathInExpr, MathTex]
            placeholder_node: Tuple[PathInExpr, Mobject]
            edges: dict[PathInExpr, Line]

        def compile_continuation(
            cont: ArithCont,
        ) -> ContinuationCompilationResult:
            def symbol_for_root_of(cont: ArithCont) -> str:
                if (
                    cont["tag"] == "cont-then-proceed-to-right-of-add-ae"
                    or cont["tag"] == "cont-then-add-lit-from-left"
                ):
                    return "+"
                elif (
                    cont["tag"] == "cont-then-proceed-to-right-of-mul-ae"
                    or cont["tag"] == "cont-then-mul-lit-from-left"
                ):
                    return "\\times"

            node_vobjs: dict[PathInExpr, MathTex]
            edge_vobjs: dict[PathInExpr, Line]

            template_node = (
                Star(outer_radius=0.15)
                .set_fill(FOCUSED_SUBTREE_COLOR, opacity=1)
                .move_to(vector2d_to_vector3d(cont["placeholder_pos"]))
                .set_color(FOCUSED_SUBTREE_COLOR)
            )

            if (
                cont["tag"] == "cont-then-add-lit-from-left"
                or cont["tag"] == "cont-then-mul-lit-from-left"
            ):
                # We then have a very simple 3-node continuation
                node_vobjs = {
                    (): MathTex(symbol_for_root_of(cont), **NODE_CONFIG)
                    .move_to(vector2d_to_vector3d(cont["symbol_pos"]))
                    .set_color(POSTPONED_SUBTREE_COLOR),
                    ("left",): MathTex(str(cont["left"]), **NODE_CONFIG)
                    .move_to(vector2d_to_vector3d(cont["literal_pos"]))
                    .set_color(POSTPONED_SUBTREE_COLOR),
                }
                edge_vobjs = {
                    ("left",): connect(
                        node_vobjs[()],
                        node_vobjs[("left",)],
                        BUFF,
                        LINE_CONFIG,
                    ).set_color(POSTPONED_SUBTREE_COLOR),
                    ("right",): connect(
                        node_vobjs[()],
                        template_node,
                        BUFF,
                        LINE_CONFIG,
                    ).set_color(POSTPONED_SUBTREE_COLOR),
                }
                return ContinuationCompilationResult(
                    node_vobjs, (("right",), template_node), edge_vobjs
                )
            else:
                # We have an expression attached to the continuation
                subexpr_nodes, subexpr_edges = compile_arith_expr(
                    cont["right"],
                    decide_color_of_edge_reaching=lambda _: POSTPONED_SUBTREE_COLOR,
                    decide_color_of_node=lambda _: POSTPONED_SUBTREE_COLOR,
                )
                node_vobjs = {
                    (): MathTex(symbol_for_root_of(cont), **NODE_CONFIG)
                    .move_to(vector2d_to_vector3d(cont["symbol_pos"]))
                    .set_color(POSTPONED_SUBTREE_COLOR),
                    **dict(
                        [
                            ((childDirectionRight,) + path, node)
                            for path, node in subexpr_nodes.items()
                        ]
                    ),
                }
                edge_vobjs = {
                    ("left",): connect(
                        node_vobjs[()],
                        template_node,
                        BUFF,
                        LINE_CONFIG,
                    ).set_color(POSTPONED_SUBTREE_COLOR),
                    ("right",): connect(
                        node_vobjs[()],
                        subexpr_nodes[()],
                        BUFF,
                        LINE_CONFIG,
                    ).set_color(POSTPONED_SUBTREE_COLOR),
                    **dict(
                        [
                            ((childDirectionRight,) + path, edge)
                            for path, edge in subexpr_edges.items()
                        ]
                    ),
                }
                return ContinuationCompilationResult(
                    node_vobjs, (("left",), template_node), edge_vobjs
                )

        # main animation
        self.wait(0.3)
        initial_expr_nodes, initial_expr_edges = compile_arith_expr(
            trace[0][0],
        )
        initial_expr_vgroup = VGroup(
            *initial_expr_nodes.values(), *initial_expr_edges.values()
        )
        self.play(
            Create(
                initial_expr_vgroup.to_edge(LEFT, buff=1).set_y(0),
                lag_ratio=0,
            )
        )

        center_of_expr = initial_expr_vgroup.get_center()
        # invariant: black expr tree and continuation stack are drawn and center_of_expr is the center of the expr tree
        for (current_expr, current_continuation_stack), (
            next_expr,
            next_continuation_stack,
        ) in zip(trace, trace[1:]):
            current_expr_black_nodes, current_expr_black_edges = compile_arith_expr(
                current_expr,
            )
            current_expr_black_vgroup = VGroup(
                *current_expr_black_nodes.values(),
                *current_expr_black_edges.values(),
            )
            current_expr_black_vgroup.move_to(center_of_expr)

            # this should be a no-op visually given the invariant
            # its purpose is to force current_expr_black_vgroup being the object drawn on the canvas
            self.clear()
            self.add(current_expr_black_vgroup)

            root_patmat_rect_0 = SurroundingRectangle(
                current_expr_black_nodes[()], color=BLUE_E, buff=0.15
            )
            self.play(
                Create(
                    root_patmat_rect_0,
                    run_time=SLEEP_BETWEEN_EXPR_PATTERN_MATCH_STEPS / 2,
                )
            )
            self.wait(SLEEP_BETWEEN_EXPR_PATTERN_MATCH_STEPS / 2)

            if current_expr["tag"] == "aexpr-int-lit":
                # in this path, we have a literal at the root so we must have popped a continuation and reconfigured the control string
                root_patmat_final_rect = SurroundingRectangle(
                    current_expr_black_nodes[()],
                    color=ORANGE,
                    buff=0.15,
                )
                self.play(
                    Succession(
                        root_patmat_rect_0.animate.scale(1.1).set_rate_func(
                            rate_functions.there_and_back
                        ),
                        ReplacementTransform(
                            root_patmat_rect_0,
                            root_patmat_final_rect,
                        ),
                        run_time=SLEEP_BETWEEN_EXPR_PATTERN_MATCH_STEPS / 2,
                    )
                )
                self.wait(SLEEP_AFTER_REDEX_IDENTIFICATION / 2)
                self.play(
                    FadeOut(root_patmat_final_rect),
                    run_time=SLEEP_BETWEEN_EXPR_PATTERN_MATCH_STEPS / 2,
                )
                self.wait(SLEEP_BETWEEN_EXPR_PATTERN_MATCH_STEPS / 2)
            else:
                # in this path, we have a non-literal at the root so we must decompose the root in either direction
                # and push a continuation to the stack

                # pattern-match at the root happens in two-steps (the first step is to confirm that the root is not a literal,
                # the second step is to identify which of left or right child should be traversed next)
                root_and_left_group = VGroup(
                    current_expr_black_nodes[()],
                    current_expr_black_nodes[("left",)],
                )
                root_patmat_left_rect = SurroundingRectangle(
                    root_and_left_group,
                    color=BLUE_E,
                    buff=0.15,
                )
                root_patmat_final_rect = SurroundingRectangle(
                    root_and_left_group,
                    color=ORANGE,
                    buff=0.15,
                )

                # first step
                self.play(
                    ReplacementTransform(
                        root_patmat_rect_0,
                        root_patmat_left_rect,
                        run_time=SLEEP_BETWEEN_EXPR_PATTERN_MATCH_STEPS / 2,
                    )
                )
                self.wait(SLEEP_BETWEEN_EXPR_PATTERN_MATCH_STEPS / 2)

                # second step: we should conceptually split the tree at this point,
                #              so we prepare a partitioned copy of the current_expr_black_vgroup tree
                #              and morph current_expr_black_vgroup into it
                we_should_proceed_left = (
                    current_expr["tag"] == "aexpr-add"
                    and current_expr["left"]["tag"] != "aexpr-int-lit"
                ) or (
                    current_expr["tag"] == "aexpr-mul"
                    and current_expr["left"]["tag"] != "aexpr-int-lit"
                )
                focus_subtree_path_prefix: PathInExpr = (
                    ("left",) if we_should_proceed_left else ("right",)
                )
                coloured_expr_nodes, coloured_expr_edges = compile_arith_expr(
                    current_expr,
                    decide_color_of_edge_reaching=lambda path: (
                        FOCUSED_SUBTREE_COLOR
                        if path[:1] == focus_subtree_path_prefix
                        and len(path)
                        > 1  # we do not want to color the edge coming from the root
                        else POSTPONED_SUBTREE_COLOR
                    ),
                    decide_color_of_node=lambda path: (
                        FOCUSED_SUBTREE_COLOR
                        if path[:1] == focus_subtree_path_prefix
                        else POSTPONED_SUBTREE_COLOR
                    ),
                )
                coloured_expr_vgroup = VGroup(
                    *coloured_expr_nodes.values(),
                    *coloured_expr_edges.values(),
                )
                coloured_expr_vgroup.move_to(center_of_expr)
                self.play(
                    Succession(
                        root_patmat_left_rect.animate.scale(1.1).set_rate_func(
                            rate_functions.there_and_back
                        ),
                        ReplacementTransform(
                            root_patmat_left_rect,
                            root_patmat_final_rect,
                        ),
                    ),
                    AnimationGroup(
                        *[
                            ReplacementTransform(
                                current_expr_black_nodes[path],
                                coloured_expr_nodes[path],
                            )
                            for path in current_expr_black_nodes
                        ],
                        *[
                            ReplacementTransform(
                                current_expr_black_edges[path],
                                coloured_expr_edges[path],
                            )
                            for path in current_expr_black_edges
                        ],
                        lag_ratio=0.1,
                    ),
                    run_time=SLEEP_BETWEEN_EXPR_PATTERN_MATCH_STEPS / 2,
                )
                self.wait(SLEEP_BETWEEN_EXPR_PATTERN_MATCH_STEPS / 2)

                next_expr_focused_color_nodes, next_expr_focused_color_edges = (
                    compile_arith_expr(
                        next_expr,
                        decide_color_of_edge_reaching=lambda _: FOCUSED_SUBTREE_COLOR,
                        decide_color_of_node=lambda _: FOCUSED_SUBTREE_COLOR,
                    )
                )
                next_expr_focused_color_vgroup = VGroup(
                    *next_expr_focused_color_nodes.values(),
                    *next_expr_focused_color_edges.values(),
                )
                next_expr_focused_color_vgroup.move_to(center_of_expr)

                (
                    new_continuation_nodes,
                    new_continuation_template_node,
                    new_continuation_edges,
                ) = compile_continuation(
                    next_continuation_stack[-1],
                )
                new_continuation_vgroup = VGroup(
                    *new_continuation_nodes.values(),
                    new_continuation_template_node[1],
                    *new_continuation_edges.values(),
                )
                new_continuation_vgroup.move_to(RIGHT * 4)

                # We successfully partitioned the tree into the immediately interesting subtree
                # and the postponed subtree. Now we need to do a few things at once:
                self.play(
                    AnimationGroup(
                        # 1. fade out the root pattern match rectangle
                        FadeOut(root_patmat_final_rect),
                        # 2. morph the immediately interesting subtree in coloured_expr_vgroup into next_expr_focused_color_vgroup, which
                        #    has its center moved to at center_of_expr
                        *[
                            ReplacementTransform(
                                coloured_expr_nodes[focus_subtree_path_prefix + path],
                                next_expr_focused_color_nodes[path],
                            )
                            for path in next_expr_focused_color_nodes
                        ],
                        *[
                            ReplacementTransform(
                                coloured_expr_edges[focus_subtree_path_prefix + path],
                                next_expr_focused_color_edges[path],
                            )
                            for path in next_expr_focused_color_edges
                        ],
                        # 3. replace the immediately interesting subtree with a symbolic placeholder (a star that is colored in "focused subtree" color),
                        #    move the so-constructed tree (which is a single continuation) to the right, pushing it to the stack.
                        *[
                            ReplacementTransform(
                                coloured_expr_nodes[path],
                                new_continuation_nodes[path],
                            )
                            for path in coloured_expr_nodes
                            if path[: len(focus_subtree_path_prefix)]
                            != focus_subtree_path_prefix
                        ],
                        *[
                            ReplacementTransform(
                                coloured_expr_edges[path],
                                new_continuation_edges[path],
                            )
                            for path in new_continuation_edges
                        ],
                        ReplacementTransform(
                            VGroup(
                                *[
                                    coloured_expr_nodes[path].copy()
                                    for path in coloured_expr_nodes
                                    if path[: len(focus_subtree_path_prefix)]
                                    == focus_subtree_path_prefix
                                ],
                                *[
                                    coloured_expr_edges[path].copy()
                                    for path in coloured_expr_edges
                                    if path[: len(focus_subtree_path_prefix)]
                                    == focus_subtree_path_prefix
                                ],
                            ),
                            new_continuation_template_node[1],
                        ),
                    ),
                    run_time=SUBTREE_DECOMPOSITION_ANIMATION_DURATION / 5 * 3,
                )
                self.wait(SUBTREE_DECOMPOSITION_ANIMATION_DURATION / 5 * 2)

                # we now de-color the focused subtree
                decoloring = (
                    *[
                        node.animate.set_color(BLACK)
                        for node in next_expr_focused_color_nodes.values()
                    ],
                    *[
                        edge.animate.set_color(BLACK)
                        for edge in next_expr_focused_color_edges.values()
                    ],
                )
                if decoloring:
                    self.play(
                        *decoloring,
                        run_time=SUBTREE_DECOMPOSITION_ANIMATION_DURATION,
                    )
                else:
                    # no decoloring to do, we just wait
                    self.wait(SUBTREE_DECOMPOSITION_ANIMATION_DURATION)

            pass

        self.wait(1)
