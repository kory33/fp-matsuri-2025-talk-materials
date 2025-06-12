from typing import (
    Any,
    Callable,
    Iterable,
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
)
from manim.typing import Vector3D
from manim.utils.color.manim_colors import *
from manim.constants import *


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
    symbol_pos: Tuple[float, float]


class MulArithExprWithNodePos(TypedDict):
    tag: Literal["aexpr-mul"]
    left: "ArithExpr"
    right: "ArithExpr"
    symbol_pos: Tuple[float, float]


class IntLitArithExprWithNodePos(TypedDict):
    tag: Literal["aexpr-int-lit"]
    value: int
    symbol_pos: Tuple[float, float]


ArithExpr = Union[
    AddArithExprWithNodePos, MulArithExprWithNodePos, IntLitArithExprWithNodePos
]


def ae_root_pos(expr: ArithExpr) -> Vector3D:
    return np.array((expr["symbol_pos"][0], expr["symbol_pos"][1], 0))


ChildDirection = Literal["left", "right"]
childDirections: Tuple[ChildDirection, ...] = ("left", "right")
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
    symbol_pos: Tuple[float, float]


class ThenAddLitFromLeftWithNodePos(TypedDict):
    tag: Literal["cont-then-add-lit-from-left"]
    left: int
    symbol_pos: Tuple[float, float]


class ThenProceedToRightOfMulAEWithNodePos(TypedDict):
    tag: Literal["cont-then-proceed-to-left-of-mul-ae"]
    left: ArithExpr
    symbol_pos: Tuple[float, float]


class ThenMulLitFromLeftWithNodePos(TypedDict):
    tag: Literal["cont-then-mul-lit-from-left"]
    left: int
    symbol_pos: Tuple[float, float]


ArithCont = Union[
    ThenProceedToRightOfAddAEWithNodePos,
    ThenAddLitFromLeftWithNodePos,
    ThenProceedToRightOfMulAEWithNodePos,
    ThenMulLitFromLeftWithNodePos,
]


class EvalWithContinuation_Expression_13479(Scene):
    background_color = WHITE

    def construct(self):
        # ─── Config ────────────────────────────────────────────────────────────
        LINE_WIDTH = 4
        BUFF = 0.3  # extra padding around each symbol’s circle

        SLEEP_BETWEEN_REDEX_IDENTIFICATION_TRAVERSALS = 0.3
        SLEEP_AFTER_REDEX_IDENTIFICATION = 0.15
        SLEEP_BETWEEN_REDUCTION_STEPS = 0.5

        NODE_CONFIG: dict[str, Any] = {"font_size": 60, "color": BLACK}
        LINE_CONFIG: dict[str, Any] = {"stroke_width": LINE_WIDTH, "color": BLACK}

        self.camera.background_color = WHITE

        expr: ArithExpr = {
            "tag": "aexpr-add",
            "left": {
                "tag": "aexpr-add",
                "left": {
                    "tag": "aexpr-add",
                    "left": {
                        "tag": "aexpr-int-lit",
                        "value": 1,
                        "symbol_pos": (-3.5, -1),
                    },
                    "right": {
                        "tag": "aexpr-int-lit",
                        "value": 3,
                        "symbol_pos": (-2, -1),
                    },
                    "symbol_pos": (-2.75, 1),
                },
                "right": {
                    "tag": "aexpr-mul",
                    "left": {
                        "tag": "aexpr-int-lit",
                        "value": 4,
                        "symbol_pos": (-0.5, -1),
                    },
                    "right": {
                        "tag": "aexpr-int-lit",
                        "value": 7,
                        "symbol_pos": (1, -1),
                    },
                    "symbol_pos": (0.25, 1),
                },
                "symbol_pos": (-1.25, 2),
            },
            "right": {"tag": "aexpr-int-lit", "value": 9, "symbol_pos": (2, 2)},
            "symbol_pos": (0, 3),
        }

        def compile_arith_expr_into_vgroup(
            expr: ArithExpr,
            decide_color_of_edge_reaching: Callable[[PathInExpr], ManimColor],
            decide_color_of_node: Callable[[PathInExpr], ManimColor],
        ) -> VGroup:
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
                        .move_to(ae_root_pos(subexpr) * 0.8)
                        .set_color(decide_color_of_node(path))
                        .scale(0.8),
                    )
                    for path, subexpr in ae_zip_nodes_with_paths(expr)
                ]
            )
            edge_vobjs = [
                connect(
                    parent_vobj,
                    node_vobjs[path + (direction,)],
                    BUFF,
                    LINE_CONFIG,
                ).set_color(decide_color_of_edge_reaching(path + (direction,)))
                for path, parent_vobj in node_vobjs.items()
                for direction in childDirections
                if (path + (direction,) in node_vobjs)
            ]

            return VGroup(node_vobjs.values(), *edge_vobjs)

        def animate_continuation_consumption(
            current_expr: IntLitArithExprWithNodePos,
            # nonempty stack of continuations
            current_stack: Tuple[ArithCont, ...],
        ) -> Tuple[ArithExpr, Tuple[ArithCont, ...]]:
            if not current_stack:
                raise ValueError("Cannot consume continuation from empty stack")

            lit = current_expr["value"]

            # pop the top continuation
            continuation = current_stack[-1]
            new_stack = current_stack[:-1]

            if continuation["tag"] == "cont-then-proceed-to-right-of-add-ae":
                return (
                    continuation["right"],
                    new_stack
                    + (
                        {
                            "tag": "cont-then-add-lit-from-left",
                            "left": lit,
                            "symbol_pos": current_expr["symbol_pos"],
                        },
                    ),
                )
            elif continuation["tag"] == "cont-then-add-lit-from-left":
                return (
                    {
                        "tag": "aexpr-int-lit",
                        "value": lit + continuation["left"],
                        "symbol_pos": current_expr["symbol_pos"],
                    },
                    new_stack,
                )
            elif continuation["tag"] == "cont-then-proceed-to-left-of-mul-ae":
                return (
                    continuation["left"],
                    new_stack
                    + (
                        {
                            "tag": "cont-then-mul-lit-from-left",
                            "left": lit,
                            "symbol_pos": current_expr["symbol_pos"],
                        },
                    ),
                )
            elif continuation["tag"] == "cont-then-mul-lit-from-left":
                return (
                    {
                        "tag": "aexpr-int-lit",
                        "value": lit * continuation["left"],
                        "symbol_pos": current_expr["symbol_pos"],
                    },
                    new_stack,
                )

        def animate_subexpr_entrance(
            current_expr: AddArithExprWithNodePos | MulArithExprWithNodePos,
            current_stack: Tuple[ArithCont, ...],
        ) -> Tuple[ArithExpr, Tuple[ArithCont, ...]]:
            if current_expr["tag"] == "aexpr-add":
                if current_expr["left"]["tag"] == "aexpr-int-lit":
                    return (
                        current_expr["right"],
                        current_stack
                        + (
                            {
                                "tag": "cont-then-add-lit-from-left",
                                "left": current_expr["left"]["value"],
                                "symbol_pos": current_expr["left"]["symbol_pos"],
                            },
                        ),
                    )
                else:
                    return (
                        current_expr["left"],
                        current_stack
                        + (
                            {
                                "tag": "cont-then-proceed-to-right-of-add-ae",
                                "right": current_expr["right"],
                                "symbol_pos": current_expr["symbol_pos"],
                            },
                        ),
                    )
            elif current_expr["tag"] == "aexpr-mul":
                if current_expr["left"]["tag"] == "aexpr-int-lit":
                    return (
                        current_expr["right"],
                        current_stack
                        + (
                            {
                                "tag": "cont-then-mul-lit-from-left",
                                "left": current_expr["left"]["value"],
                                "symbol_pos": current_expr["left"]["symbol_pos"],
                            },
                        ),
                    )
                else:
                    return (
                        current_expr["left"],
                        current_stack
                        + (
                            {
                                "tag": "cont-then-proceed-to-left-of-mul-ae",
                                "left": current_expr["right"],
                                "symbol_pos": current_expr["symbol_pos"],
                            },
                        ),
                    )

        # main animation
        self.wait(0.3)
        self.play(
            Create(
                compile_arith_expr_into_vgroup(
                    expr,
                    decide_color_of_edge_reaching=lambda path: BLACK,
                    decide_color_of_node=lambda path: BLACK,
                ).to_edge(LEFT, buff=1),
                lag_ratio=0,
            )
        )
        self.wait(0.3)

        # state variables
        # these get updated destructively during the animation
        current_expr_of_interest = expr
        continuation_stack: Tuple[ArithCont, ...] = ()

        while True:
            if current_expr_of_interest["tag"] == "aexpr-int-lit":
                if not continuation_stack:
                    # no continuation left, we are done
                    break
                else:
                    current_expr_of_interest, continuation_stack = (
                        animate_continuation_consumption(
                            current_expr_of_interest,
                            continuation_stack,
                        )
                    )
            else:
                current_expr_of_interest, continuation_stack = animate_subexpr_entrance(
                    current_expr_of_interest,
                    continuation_stack,
                )

        self.wait(1)
