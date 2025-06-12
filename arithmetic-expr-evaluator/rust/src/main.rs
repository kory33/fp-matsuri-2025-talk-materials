#![warn(clippy::pedantic)]

#[derive(Debug, Clone)]
enum Expr {
    Lit(i32),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
}

fn test_expr() -> Expr {
    // (3 + 6) + (2 * 5)
    Expr::Add(
        Box::new(Expr::Add(Box::new(Expr::Lit(3)), Box::new(Expr::Lit(6)))),
        Box::new(Expr::Mul(Box::new(Expr::Lit(2)), Box::new(Expr::Lit(5)))),
    )
}

fn eval_one_step(expr: Expr) -> Expr {
    match expr {
        Expr::Add(left, right) => {
            if let Expr::Lit(l) = *left {
                if let Expr::Lit(r) = *right {
                    Expr::Lit(l + r)
                } else {
                    Expr::Add(left, Box::new(eval_one_step(*right)))
                }
            } else {
                Expr::Add(Box::new(eval_one_step(*left)), right)
            }
        }
        Expr::Mul(left, right) => {
            if let Expr::Lit(l) = *left {
                if let Expr::Lit(r) = *right {
                    Expr::Lit(l * r)
                } else {
                    Expr::Mul(left, Box::new(eval_one_step(*right)))
                }
            } else {
                Expr::Mul(Box::new(eval_one_step(*left)), right)
            }
        }
        Expr::Lit(_) => expr, // No operation needed for literals
    }
}

fn eval(expr: &Expr) -> i32 {
    let mut current_expr = expr.clone();
    loop {
        let next_expr = eval_one_step(current_expr);
        if let Expr::Lit(l) = next_expr {
            return l;
        }
        current_expr = next_expr;
    }
}

fn eval_with_control_string_and_continuation(expr: &Expr) -> i32 {
    #[derive(Debug)]
    enum Continuation {
        // "★ + {expr}" の形をした継続。
        // これはつまり、「次の私」への
        //   『「今の私」が左側の部分木を簡約した結果を遺すはずなので、それを ThenAddLitFromLeft として書き残した上で
        //     右側の部分木の簡約に勤しむべきだ』
        // という期待になっている。
        ThenProceedToRightSubtreeOfAdd(Box<Expr>),
        // "{lit} + ★" の形をした継続。
        // これはつまり、「次の私」への
        //   『「今の私」が右側の部分木を簡約した結果を遺すはずなので、それに左側に入っていたリテラルを足して
        //     リテラルを得るという計算をするべきだ』
        // という期待になっている。
        ThenAddLitFromLeft(i32),

        // "★ × {expr}" の形をした継続。ThenProceedToRightSubtreeOfAdd と同様の (もちろん、+ を × に置き換えた版の) 期待に対応する。
        ThenProceedToRightSubtreeOfMul(Box<Expr>),
        // "{lit} × ★" の形をした継続。ThenAddLitFromLeft と同様の (もちろん、+ を × に置き換えた版の) 期待に対応する。
        ThenMulLitFromLeft(i32),
    }

    // 「期待の書き置き」を遺す場所。この場所自体はすべての「私」が表面的には共有しているが、
    // 実際のところ、一番上（Vec の末尾）に対してしか誰も読み書きをせず、Vec の各セルが
    // single-sender-single-receiver なチャンネルとして機能する。
    let mut expectation_stack: Vec<Continuation> = Vec::new();

    // 「今の私」が評価に取り組まなければならない式。一番最初の時点では、expr 全体になっている。
    let mut the_thing_i_need_to_work_on = expr.clone();

    loop {
        match the_thing_i_need_to_work_on {
            Expr::Add(left, right) => {
                if let Expr::Lit(l) = *left {
                    // 左側はもう見なくていいので、右側を見に行く。
                    // 左側の値を足して簡約するというところは、この時点での私をクローンした「次の私」に託す。
                    expectation_stack.push(Continuation::ThenAddLitFromLeft(l));
                    the_thing_i_need_to_work_on = *right;
                } else {
                    // + の左側がリテラルでないなら、まずは左側を処理しないといけない。
                    // 右側の処理は、この時点での私をクローンした「次の私」に託す。
                    expectation_stack.push(Continuation::ThenProceedToRightSubtreeOfAdd(right));
                    the_thing_i_need_to_work_on = *left;

                    // NOTE: 元々の the_thing_i_need_to_work_on （つまり Expr::Add(left, right)） のうち、
                    //       「今の私」は left の所有権を奪い、right の所有権は expectation_stack に押し付けている。
                    //       expectation_stack に押し付けられたものは（「今の私」は木の末端まで見たら力尽きてしまうので）「今の私」が触ることは
                    //       もう二度となく、そのまま「次の私」が引き継ぐことになる。この所有権の分割という現象こそ、
                    //       Kory が「今の私」とそのクローンというアナロジーを持ち出してきている理由である。
                    //       一般に、非決定性計算を特定の順番に線形化した逐次計算というのは全く同じ構造を持つ。
                }
            }
            Expr::Mul(left, right) => {
                if let Expr::Lit(l) = *left {
                    // 左側はもう見なくていいので、右側を見に行く。
                    // 左側の値を足して簡約するというところは、この時点での私をクローンした「次の私」に託す。
                    expectation_stack.push(Continuation::ThenMulLitFromLeft(l));
                    the_thing_i_need_to_work_on = *right;
                } else {
                    // × の左側がリテラルでないなら、まずは左側を処理しないといけない。
                    // 右側の処理は、この時点での私をクローンした「次の私」に託す。
                    expectation_stack.push(Continuation::ThenProceedToRightSubtreeOfMul(right));
                    the_thing_i_need_to_work_on = *left;
                }
            }
            Expr::Lit(l) => {
                // 「前の私」はもう Expr::Lit(l) を見た瞬間に力尽きており、「今の私」は、「前の私」が分岐時点で遺したクローンになっている。
                // 「前の私」が託してきた期待 (continuation_stack.pop()) というのをここで引き継がねばならない。
                match expectation_stack.pop() {
                    Some(Continuation::ThenProceedToRightSubtreeOfAdd(right)) => {
                        // 『「前の私」が左側の部分木を簡約結果を l として遺したわけなので、それを ThenAddLitFromLeft として書き残した上で
                        //   右側の部分木の簡約に勤しむべき』
                        expectation_stack.push(Continuation::ThenAddLitFromLeft(l));
                        the_thing_i_need_to_work_on = *right;
                    }
                    Some(Continuation::ThenAddLitFromLeft(left)) => {
                        // 『「前の私」が右側の部分木を簡約結果を l として遺したわけなので、それに左側に入っているリテラルを足して
                        //   リテラルを得るという計算をするべき』
                        the_thing_i_need_to_work_on = Expr::Lit(left + l);
                    }
                    Some(Continuation::ThenProceedToRightSubtreeOfMul(right)) => {
                        // 『「前の私」が左側の部分木を簡約結果を l として遺したわけなので、それを ThenMulLitFromLeft として書き残した上で
                        //   右側の部分木の簡約に勤しむべき』
                        expectation_stack.push(Continuation::ThenMulLitFromLeft(l));
                        the_thing_i_need_to_work_on = *right;
                    }
                    Some(Continuation::ThenMulLitFromLeft(left)) => {
                        // 『「前の私」が右側の部分木を簡約結果を l として遺したわけなので、それに左側に入っているリテラルを掛けて
                        //   リテラルを得るという計算をするべき』
                        the_thing_i_need_to_work_on = Expr::Lit(left * l);
                    }
                    None => {
                        // 「前の私」（もしそのような存在が居たのならば…）が私に託したことは何もなく、
                        // 簡約結果はすでに遺されている（あるいは、最初からそこにはリテラルしかなかった）。
                        // これを結果として持ち帰れば良い。
                        return l;
                    }
                }
            }
        }
    }
}

fn main() {
    println!("eval({:?}) = {}", test_expr(), eval(&test_expr()));
    println!(
        "eval_with_control_string_and_continuation({:?}) = {}",
        test_expr(),
        eval_with_control_string_and_continuation(&test_expr())
    );
}
