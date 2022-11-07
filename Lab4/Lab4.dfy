datatype Val = Undef | Int(i: int) | Bool(b: bool)

datatype AExp =
    Val(val: Val) |
    Var(name: string) |
    Plus(lhs: AExp, rhs: AExp) |
    Minus(lhs: AExp, rhs: AExp) |
    Mul(lhs: AExp, rhs: AExp) |
    Div(lhs: AExp, rhs: AExp) |
    Mod(lhs: AExp, rhs: AExp)

datatype BExp =
    Val(val: Val) |
    Var(name: string) |
    Gt(lhs: AExp, rhs: AExp) |
    Geq(lhs: AExp, rhs: AExp) |
    Lt(lhs: AExp, rhs: AExp) |
    Leq(lhs: AExp, rhs: AExp) |
    Eq(lhs: AExp, rhs: AExp) |

    And(left: BExp, right: BExp) |
    Or(left: BExp, right: BExp) |
    Xor(left: BExp, right: BExp) |
    Not(bexp: BExp)

datatype Exp = AExp(aexp: AExp) | BExp(bexp: BExp)

datatype Stmt =
    Exp(exp: Exp) |
    Assign(x: string, Exp) |
    Blk(stmts: seq<Stmt>) |
    If(cond: BExp, stmt: Stmt) |
    Ite(cond: BExp, stmt1: Stmt, stmt2: Stmt) |
    While(cond: BExp, stmt: Stmt)


predicate BigStepAExp (
    aexp: AExp, 
    init: map<string, Val>, 
    final: map<string, Val>, 
    val: Val
) {
    match aexp
        case Val(val') => val' == val && final == init
        case Var(v) => if v in init then init[v] == val && final == init else false
        case Plus(ae1, ae2) => 
            exists v1: Val, v2: Val, sigma1: map<string, Val> :: (
                BigStepAExp(ae1, init, sigma1, v1) && 
                BigStepAExp(ae2, sigma1, final, v2) &&
                v1.Int? && v2.Int? && val.Int? &&
                v1.i + v2.i == val.i
            )
        case Minus(ae1, ae2) => 
            exists v1: Val, v2: Val, sigma1: map<string, Val> :: (
                BigStepAExp(ae1, init, sigma1, v1) && 
                BigStepAExp(ae2, sigma1, final, v2) &&
                v1.Int? && v2.Int? && val.Int? &&
                v1.i - v2.i == val.i
            )
        case Mul(ae1, ae2) => 
            exists v1: Val, v2: Val, sigma1: map<string, Val> :: (
                BigStepAExp(ae1, init, sigma1, v1) && 
                BigStepAExp(ae2, sigma1, final, v2) &&
                v1.Int? && v2.Int? && val.Int? &&
                v1.i * v2.i == val.i
            )
        case Div(ae1, ae2) => 
            exists v1: Val, v2: Val, sigma1: map<string, Val> :: (
                BigStepAExp(ae1, init, sigma1, v1) && 
                BigStepAExp(ae2, sigma1, final, v2) &&
                v1.Int? && v2.Int? && val.Int? &&
                v2.i != 0 &&
                v1.i / v2.i == val.i
            )
        case Mod(ae1, ae2) => 
            exists v1: Val, v2: Val, sigma1: map<string, Val> :: (
                BigStepAExp(ae1, init, sigma1, v1) && 
                BigStepAExp(ae2, sigma1, final, v2) &&
                v1.Int? && v2.Int? && val.Int? &&
                v2.i != 0 &&
                v1.i % v2.i == val.i
            )
}

predicate BigStepBExp (
    bexp: BExp, 
    init: map<string, Val>, 
    final: map<string, Val>, 
    val: Val) 
{
    match bexp
        case Val(val') => val' == val && final == init
        case Var(v) => if v in init then init[v] == val && final == init else false
        case Gt(ae1, ae2) => 
            exists v1: Val, v2: Val, sigma1: map<string, Val> :: (
                BigStepAExp(ae1, init, sigma1, v1) && 
                BigStepAExp(ae2, sigma1, final, v2) &&
                v1.Int? && v2.Int? && val.Bool? &&
                (v1.i > v2.i) == val.b
            )
        case Geq(ae1, ae2) => 
            exists v1: Val, v2: Val, sigma1: map<string, Val> :: (
                BigStepAExp(ae1, init, sigma1, v1) && 
                BigStepAExp(ae2, sigma1, final, v2) &&
                v1.Int? && v2.Int? && val.Bool? &&
                (v1.i >= v2.i) == val.b
            )
        case Lt(ae1, ae2) => 
            exists v1: Val, v2: Val, sigma1: map<string, Val> :: (
                BigStepAExp(ae1, init, sigma1, v1) && 
                BigStepAExp(ae2, sigma1, final, v2) &&
                v1.Int? && v2.Int? && val.Bool? &&
                (v1.i < v2.i) == val.b
            )
        case Leq(ae1, ae2) => 
            exists v1: Val, v2: Val, sigma1: map<string, Val> :: (
                BigStepAExp(ae1, init, sigma1, v1) && 
                BigStepAExp(ae2, sigma1, final, v2) &&
                v1.Int? && v2.Int? && val.Bool? &&
                (v1.i <= v2.i) == val.b
            )
        case Eq(ae1, ae2) => 
            exists v1: Val, v2: Val, sigma1: map<string, Val> :: (
                BigStepAExp(ae1, init, sigma1, v1) && 
                BigStepAExp(ae2, sigma1, final, v2) &&
                v1.Int? && v2.Int? && val.Bool? &&
                (v1.i == v2.i) == val.b
            )

        case And(be1, be2) => 
            exists b1: Val, b2: Val, sigma1: map<string, Val> :: (
                BigStepBExp(be1, init, sigma1, b1) && 
                BigStepBExp(be2, sigma1, final, b2) &&
                b1.Bool? && b2.Bool? && val.Bool? &&
                (b1.b && b2.b) == val.b
            )
        case Or(be1, be2) => 
            exists b1: Val, b2: Val, sigma1: map<string, Val> :: (
                BigStepBExp(be1, init, sigma1, b1) && 
                BigStepBExp(be2, sigma1, final, b2) &&
                b1.Bool? && b2.Bool? && val.Bool? &&
                (b1.b || b2.b) == val.b
            )
        case Xor(be1, be2) => 
            exists b1: Val, b2: Val, sigma1: map<string, Val> :: (
                BigStepBExp(be1, init, sigma1, b1) && 
                BigStepBExp(be2, sigma1, final, b2) &&
                b1.Bool? && b2.Bool? && val.Bool? &&
                ((b1.b == true && b2.b == false) ||
                (b1.b == false && b2.b == true)) == val.b
            )
        case Not(bexp) => 
            exists boolean: Val :: (
                BigStepBExp(bexp, init, final, boolean) && 
                boolean.Bool? && val.Bool? &&
                (!boolean.b == val.b)
            )
}

/* Exercise 3
 * The BigStep evaluation of AExps and BExps is deterministic 
 * because we impose the order of evaluation between the expressions,
 * thus the generated parse tree is always the same.
 */

function update (
    state: map<string, Val>,
    x: string,
    v: Val
): map<string, Val> {
    state[x := v]
}


predicate BigStepStmt (
    stmt: Stmt, 
    init: map<string, Val>, 
    final: map<string, Val>,
    gas: nat
) decreases gas, stmt {
    match stmt
        case Exp(e) => 
            exists v: Val ::
                if e.AExp? then BigStepAExp(e.aexp, init, final, v) && v.Int? else BigStepBExp(e.bexp, init, final, v) && v.Bool?
        case Assign(x, e) => 
            exists v: Val, sigma1: map<string, Val> ::
                if e.AExp? then 
                    BigStepAExp(e.aexp, init, sigma1, v) && 
                    v.Int? && 
                    update(sigma1, x, v) == final 
                else 
                    BigStepBExp(e.bexp, init, sigma1, v) && 
                    v.Bool? && 
                    update(sigma1, x, v) == final
        case Blk(stmts) =>
            if |stmts| == 0 then
                init == final
            else
                exists sigma1: map<string, Val>, gas': nat :: 
                    gas' < gas &&
                    BigStepStmt(stmts[0], init, sigma1, gas') &&
                    BigStepStmt(Blk(stmts[1..]), sigma1, final, gas')
        case If(cond, stmt') =>
            exists b: Val, sigma1: map<string, Val>, gas': nat ::
                gas' < gas &&
                BigStepBExp(cond, init, sigma1, b) &&
                if (b.Bool?) then
                    if (b.b) then 
                        BigStepStmt(stmt', sigma1, final, gas')
                    else 
                        sigma1 == final
                else 
                    false
        case Ite(cond, stmt1, stmt2) =>
            exists b: Val, sigma1: map<string, Val>, gas': nat ::
                gas' < gas &&
                BigStepBExp(cond, init, sigma1, b) &&
                if (b.Bool?) then
                    if (b.b) then 
                        BigStepStmt(stmt1, sigma1, final, gas')
                    else 
                        BigStepStmt(stmt2, sigma1, final, gas')
                else 
                    false
        case While(cond, stmt') =>
            exists b: Val, sigma1: map<string, Val>, gas': nat ::
                gas' < gas &&
                BigStepBExp(cond, init, sigma1, b) &&
                if (b.Bool?) then
                    if (b.b) then 
                        BigStepStmt(Blk([stmt', While(cond, stmt')]), sigma1, final, gas')
                    else 
                        sigma1 == final
                else 
                    false           
}

/* Exercise 5
 * The BigStep evaluation of Stmts is deterministic 
 * because we impose the order of evaluation between the statements,
 * thus the generated parse tree is always the same, given that
 * the underlying evaluation of expressions is also deterministic.
 */

lemma AddXToYCorrect(x: int, y: int)
    ensures BigStepAExp(Plus(AExp.Val(Val.Int(x)), AExp.Val(Val.Int(y))), map [], map [], Val.Int(x + y)) == true;
{
    var ae1 := AExp.Val(Val.Int(x));
    var ae2 := AExp.Val(Val.Int(y));
    
    var init := map [];
    var sigma1 := map [];
    var final := map [];

    var v1 := Val.Int(x);
    var v2 := Val.Int(y);

    var val := Val.Int(x + y);

    calc <== {
        BigStepAExp(Plus(AExp.Val(Val.Int(x)), AExp.Val(Val.Int(y))), map [], map [], Val.Int(x + y));

        BigStepAExp(ae1, init, sigma1, v1) && 
        BigStepAExp(ae2, sigma1, final, v2) &&
        v1.Int? && v2.Int? && val.Int? &&
        v1.i + v2.i == val.i;
    }
}

lemma XSmallerThanY(x: int, y: int)
    requires x < y
    ensures BigStepBExp(Lt(AExp.Var("x"), AExp.Var("y")), map ["x" := Val.Int(x), "y" := Val.Int(y)], map ["x" := Val.Int(x), "y" := Val.Int(y)], Val.Bool(true)) == true;
{
    var ae1 := AExp.Var("x");
    var ae2 := AExp.Var("y");

    var init := map ["x" := Val.Int(x), "y" := Val.Int(y)];
    var sigma1 := map ["x" := Val.Int(x), "y" := Val.Int(y)];
    var final := map ["x" := Val.Int(x), "y" := Val.Int(y)];

    var v1 := Val.Int(x);
    var v2 := Val.Int(y);

    var val := Val.Bool(true);
    
    calc <== {
        BigStepBExp(Lt(AExp.Var("x"), AExp.Var("y")), map ["x" := Val.Int(x), "y" := Val.Int(y)], map ["x" := Val.Int(x), "y" := Val.Int(y)], Val.Bool(true));

        BigStepAExp(ae1, init, sigma1, v1) && 
        BigStepAExp(ae2, sigma1, final, v2) &&
        v1.Int? && v2.Int? && val.Bool? &&
        (v1.i < v2.i) == val.b;
    }
}

lemma XGetsYCorrect(x1: int, y1: int) 
    ensures BigStepStmt(Assign("x", Exp.AExp(AExp.Var("y"))), map["x" := Val.Int(x1), "y" := Val.Int(y1)], map["x" := Val.Int(y1), "y" := Val.Int(y1)], 1000) == true;
{   
    var e := Exp.AExp(AExp.Var("y"));

    var init := map["x" := Val.Int(x1), "y" := Val.Int(y1)];
    var sigma1 := map["x" := Val.Int(x1), "y" := Val.Int(y1)];
    var final := map["x" := Val.Int(y1), "y" := Val.Int(y1)];

    var x := "x";
    var v := Val.Int(y1);

    var val := Val.Int(y1);

    var value := "y";


    calc <== {
        assert e.AExp? == true;

        BigStepStmt(Assign("x", Exp.AExp(AExp.Var("y"))), map["x" := Val.Int(x1), "y" := Val.Int(y1)], map["x" := Val.Int(y1), "y" := Val.Int(y1)], 1000);

        BigStepAExp(e.aexp, init, sigma1, v) && 
        v.Int? && 
        update(sigma1, x, v) == final;

        if value in init.Keys then init[value] == val && final == update(sigma1, x, v) else false;
    }
}

lemma TwoSquaredCorrect()
    ensures BigStepStmt(
        While (
                Lt (AExp.Var("p"), AExp.Var("n")),
                Blk (
                    [Assign (
                        "x",
                        Exp.AExp(Mul(
                            AExp.Var("x"),
                            AExp.Val(Val.Int(2))
                        ))
                    ),
                    Assign (
                        "p",
                        Exp.AExp(Plus(
                            AExp.Var("p"),
                            AExp.Val(Val.Int(1))
                        ))
                    )]
                )
        ),
        map [
            "x" := Val.Int(1),
            "p" := Val.Int(0),
            "n" := Val.Int(2)
        ],
        map [
            "x" := Val.Int(4),
            "p" := Val.Int(2),
            "n" := Val.Int(2)
        ], 
        1000
    ) == true;
{
    var gas := 1000;

    var cond := Lt (AExp.Var("p"), AExp.Var("n"));
    var init := map [
                "x" := Val.Int(1),
                "p" := Val.Int(0),
                "n" := Val.Int(2)
            ];
    var final := map [
            "x" := Val.Int(4),
            "p" := Val.Int(2),
            "n" := Val.Int(2)
        ];
    var sigma1 := map [
                "x" := Val.Int(1),
                "p" := Val.Int(0),
                "n" := Val.Int(2)
            ];
    var b := Val.Bool(true);
    var stmt' := Blk (
                        [Assign (
                            "x",
                            Exp.AExp(Mul(
                                AExp.Var("x"),
                                AExp.Val(Val.Int(2))
                            ))
                        ),
                        Assign (
                            "p",
                            Exp.AExp(Plus(
                                AExp.Var("p"),
                                AExp.Val(Val.Int(1))
                            ))
                        )]
                    );
    var gas' := 999;

    var ae1 := AExp.Var("p");
    var ae2 := AExp.Var("n");
    var v1 := Val.Int(0);
    var v2 := Val.Int(2);
    var val := Val.Bool(true);

    var stmts := [stmt', While(cond, stmt')];
    var gas'1 := 998;
    var sigma2 := map [
                "x" := Val.Int(2),
                "p" := Val.Int(1),
                "n" := Val.Int(2)
            ];

    calc <== {
        assert b.Bool?;
        assert b.b;

        BigStepStmt(
            While (
                    Lt (AExp.Var("p"), AExp.Var("n")),
                    Blk (
                        [Assign (
                            "x",
                            Exp.AExp(Mul(
                                AExp.Var("x"),
                                AExp.Val(Val.Int(2))
                            ))
                        ),
                        Assign (
                            "p",
                            Exp.AExp(Plus(
                                AExp.Var("p"),
                                AExp.Val(Val.Int(1))
                            ))
                        )]
                    )
            ),
            map [
                "x" := Val.Int(1),
                "p" := Val.Int(0),
                "n" := Val.Int(2)
            ],
            map [
                "x" := Val.Int(4),
                "p" := Val.Int(2),
                "n" := Val.Int(2)
            ], 
            1000
        );

        BigStepBExp(cond, init, sigma1, b) &&
                if (b.Bool?) then
                    if (b.b) then 
                        BigStepStmt(Blk([stmt', While(cond, stmt')]), sigma1, final, gas')
                    else 
                        sigma1 == final
                else 
                    false;

        BigStepAExp(ae1, init, sigma1, v1) && 
        BigStepAExp(ae2, sigma1, final, v2) &&
        v1.Int? && v2.Int? && val.Bool? &&
        (v1.i < v2.i) == val.b;

        if |stmts| == 0 then
                init == final
            else
                gas' < gas &&
                BigStepStmt(stmts[0], init, sigma1, gas') &&
                BigStepStmt(Blk(stmts[1..]), sigma1, final, gas');

        BigStepStmt(stmts[0], sigma1, sigma2, gas'1) &&
        BigStepStmt(Blk(stmts[1..]), sigma2, final, gas'1);

        // ...
    }
}

/*
 * SmallStep evaluation of statements is done at an operation level
 * and can be done both left-first and right-first and that means
 * that for the same statements, multiple parse trees can be generated.
 *
 * SmallStep evaluation can yield the same results by choosing a certain order
 * of evaluation (left-first, in this case) as its BigStep counterpart.
 */