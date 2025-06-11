from manim import *

# Vibe-coded almost entirely with o4-mini-high
# https://chatgpt.com/share/6849cb15-b9c4-8000-9c96-2a8db0c9b9ae

class FoldExpressionTree(Scene):
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
        self.play(*[Create(node) for node in nodes])

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
        self.play(Create(edges, lag_ratio=0))
        self.wait(SLEEP_BETWEEN_REDUCTION_STEPS)

        # ─── 3) Collapse (3 + 6) → 9 ───────────────────────────────────────────
        sub1 = VGroup(left_plus, leaf3, leaf6,
                      # we’ll also need to remove those two edges
                      edges[2], edges[3])
        box1 = SurroundingRectangle(sub1, color=ORANGE, buff=0.3)
        self.play(Create(box1))
        self.wait(SLEEP_AFTER_REDEX_IDENTIFICATION)
        const9 = MathTex("9", **NODE_CONFIG).move_to(left_plus.get_center())
        self.play(ReplacementTransform(sub1, const9), FadeOut(box1), run_time=0.6)
        self.wait(SLEEP_BETWEEN_REDUCTION_STEPS)

        # ─── 4) Collapse (2 × 5) → 10 ──────────────────────────────────────────
        # note: edges[4] and edges[5] correspond to right_times→2 and →5
        sub2 = VGroup(right_times, leaf2, leaf5, edges[4], edges[5])
        box2 = SurroundingRectangle(sub2, color=ORANGE, buff=0.3)
        self.play(Create(box2))
        self.wait(SLEEP_AFTER_REDEX_IDENTIFICATION)
        const10 = MathTex("10", **NODE_CONFIG).move_to(right_times.get_center())
        self.play(ReplacementTransform(sub2, const10), FadeOut(box2), run_time=0.6)
        self.wait(SLEEP_BETWEEN_REDUCTION_STEPS)

        # ─── 5) Collapse (9 + 10) → 19 ─────────────────────────────────────────
        # edges[0] & edges[1] are root→left_plus and root→right_times
        sub3 = VGroup(root, const9, const10, edges[0], edges[1])
        box3 = SurroundingRectangle(sub3, color=ORANGE, buff=0.3)
        self.play(Create(box3))
        self.wait(SLEEP_AFTER_REDEX_IDENTIFICATION)
        const19 = MathTex("19", **NODE_CONFIG).move_to(root.get_center())
        self.play(ReplacementTransform(sub3, const19), FadeOut(box3), run_time=0.6)
        self.wait(SLEEP_BETWEEN_REDUCTION_STEPS)
