from manim import *

# Vibe-coded with o4-mini-high and then edited
# https://chatgpt.com/share/6849cb15-b9c4-8000-9c96-2a8db0c9b9ae

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

        # ─── 1) Place the nodes ─────────────────────────────────────────────────
        root        = MathTex("+", **NODE_CONFIG).move_to(UP * 2)
        left_plus   = MathTex("+", **NODE_CONFIG).move_to(LEFT * 2)
        right_times = MathTex("\\times", **NODE_CONFIG).move_to(RIGHT * 2)
        leaf3       = MathTex("3", **NODE_CONFIG).move_to(LEFT * 3 + DOWN * 2)
        leaf6       = MathTex("6", **NODE_CONFIG).move_to(LEFT * 1 + DOWN * 2)
        leaf2       = MathTex("2", **NODE_CONFIG).move_to(RIGHT * 1 + DOWN * 2)
        leaf5       = MathTex("5", **NODE_CONFIG).move_to(RIGHT * 3 + DOWN * 2)

        nodes = [root, left_plus, right_times, leaf3, leaf6, leaf2, leaf5]
        self.wait(0.3)
        # move the tree to the left
        nodes_group = VGroup(*nodes)
        nodes_group.to_edge(LEFT, buff=1)
        self.play(Create(nodes_group, lag_ratio=0))

        # ─── 2) “Circle‐aware” connector ────────────────────────────────────────
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

        # draw all edges
        edges = VGroup(
            connect(root, left_plus),
            connect(root, right_times),
            connect(left_plus, leaf3),
            connect(left_plus, leaf6),
            connect(right_times, leaf2),
            connect(right_times, leaf5),
        )

        # ─── 2.5) Expression view ────────────────────────────────────────────────
        expr = MathTex("(3+6)", "+", "(2\\times5)", arg_separator="", **NODE_CONFIG).scale(0.8).to_edge(RIGHT, buff=1)

        self.play(Create(VGroup(edges, expr), lag_ratio=0))
        self.wait(SLEEP_BETWEEN_REDUCTION_STEPS)

        # ─── 3) Collapse (3 + 6) → 9 ───────────────────────────────────────────
        sub1 = VGroup(left_plus, leaf3, leaf6,
                      # we’ll also need to remove those two edges
                      edges[2], edges[3])
        box1 = SurroundingRectangle(sub1, color=ORANGE, buff=0.3)
        box1_expr = SurroundingRectangle(expr.get_part_by_tex("(3+6)"), color=ORANGE, buff=0.1)
        self.play(Create(box1), Create(box1_expr))
        self.wait(SLEEP_AFTER_REDEX_IDENTIFICATION)
        const9 = MathTex("9", **NODE_CONFIG).move_to(left_plus.get_center())
        box1_new = SurroundingRectangle(const9, color=ORANGE, buff=0.1)
        const9_expr = MathTex("9", "+", "(2\\times5)", arg_separator="", **NODE_CONFIG).scale(0.8).to_edge(RIGHT, buff=2)
        box1_expr_new = SurroundingRectangle(const9_expr.get_part_by_tex("9"), color=ORANGE, buff=0.1)
        self.play(
            ReplacementTransform(sub1, const9),
            ReplacementTransform(box1, box1_new),
            ReplacementTransform(expr, const9_expr),
            ReplacementTransform(box1_expr, box1_expr_new),
            run_time=0.6
        )
        expr = const9_expr
        self.play(FadeOut(box1_new), FadeOut(box1_expr_new), run_time = SLEEP_BETWEEN_REDUCTION_STEPS / 2)
        self.wait(SLEEP_BETWEEN_REDUCTION_STEPS / 2)

        # ─── 4) Collapse (2 × 5) → 10 ──────────────────────────────────────────
        sub2 = VGroup(right_times, leaf2, leaf5, edges[4], edges[5])
        box2 = SurroundingRectangle(sub2, color=ORANGE, buff=0.3)
        box2_expr = SurroundingRectangle(expr.get_part_by_tex("(2\\times5)"), color=ORANGE, buff=0.1)
        self.play(Create(box2), Create(box2_expr))
        self.wait(SLEEP_AFTER_REDEX_IDENTIFICATION)
        const10 = MathTex("10", **NODE_CONFIG).move_to(right_times.get_center())
        box2_new = SurroundingRectangle(const10, color=ORANGE, buff=0.1)
        const10_expr = MathTex("9", "+", "10", **NODE_CONFIG).scale(0.8).to_edge(RIGHT, buff=3)
        box2_expr_new = SurroundingRectangle(const10_expr.get_part_by_tex("10"), color=ORANGE, buff=0.1)
        self.play(
            ReplacementTransform(sub2, const10),
            ReplacementTransform(box2, box2_new),
            ReplacementTransform(expr, const10_expr),
            ReplacementTransform(box2_expr, box2_expr_new),
            run_time=0.6
        )
        expr = const10_expr
        self.play(FadeOut(box2_new), FadeOut(box2_expr_new), run_time = SLEEP_BETWEEN_REDUCTION_STEPS / 2)
        self.wait(SLEEP_BETWEEN_REDUCTION_STEPS / 2)

        # ─── 5) Collapse (9 + 10) → 19 ─────────────────────────────────────────
        sub3 = VGroup(root, const9, const10, edges[0], edges[1])
        box3 = SurroundingRectangle(sub3, color=ORANGE, buff=0.3)
        box3_expr = SurroundingRectangle(expr, color=ORANGE, buff=0.1)
        self.play(Create(box3), Create(box3_expr))
        self.wait(SLEEP_AFTER_REDEX_IDENTIFICATION)
        const19 = MathTex("19", **NODE_CONFIG).move_to(root.get_center())
        box3_new = SurroundingRectangle(const19, color=ORANGE, buff=0.1)
        const19_expr = MathTex("19", **NODE_CONFIG).scale(0.8).to_edge(RIGHT, buff=3)
        box3_expr_new = SurroundingRectangle(const19_expr, color=ORANGE, buff=0.1)
        self.play(
            ReplacementTransform(sub3, const19),
            ReplacementTransform(box3, box3_new),
            ReplacementTransform(expr, const19_expr),
            ReplacementTransform(box3_expr, box3_expr_new),
            run_time=0.6
        )
        self.play(FadeOut(box3_new), FadeOut(box3_expr_new), run_time = SLEEP_BETWEEN_REDUCTION_STEPS / 2)
        self.wait(SLEEP_BETWEEN_REDUCTION_STEPS / 2)
