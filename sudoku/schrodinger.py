import z3


def main():
    """
    Is Schrödinger’s cat alive or dead?

    1. Schrödinger’s cat is alive.
    2. Schrödinger’s cat is dead.
    3. Exactly one of statements 6 and 9 is true.
    4. Exactly one of statements 2 and 6 is false.
    5. Statements 4, 5 and 10 are all false.
    6. Exactly one of statements 1 and 10 is false.
    7. Exactly 5 statements are true.
    8. Exactly one of statements 3 and 10 is false.
    9. Exactly one of statements 6 and 10 is true.
    10. Exactly one of statements 1 and 2 is false.
    11. Statements 1, 8 and 11 are all false.
    """
    s = z3.Solver()

    bool_val = z3.Function("bool_val", z3.BoolSort(), z3.IntSort())
    s.add(bool_val(True) == 1)
    s.add(bool_val(False) == 0)

    # The state of the cat
    cat_alive = z3.Bool("cat-alive")

    s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11 = z3.Bools("s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11")
    # 1. Schrödinger’s cat is alive.
    # The truth of statement 1 is equivalent to the truth of act_alive
    s.add(s1 == cat_alive)

    # 2. Schrödinger’s cat is dead.
    s.add(s2 != cat_alive)

    # 3. Exactly one of statements 6 and 9 is true.
    s.add(s3 == z3.Xor(s6, s9))

    # 4. Exactly one of statements 2 and 6 is false.
    s.add(s4 == z3.Xor(s2, s6))

    # 5. Statements 4, 5 and 10 are all false.
    s.add(s5 == z3.And(z3.Not(s4), z3.Not(s5), z3.Not(s10)))

    # 6. Exactly one of statements 1 and 10 is false.
    s.add(s6 == z3.Xor(s1, s10))

    # 7. Exactly 5 statements are true.
    s.add(s7 == (bool_val(s1) +
                 bool_val(s2) +
                 bool_val(s3) +
                 bool_val(s4) +
                 bool_val(s5) +
                 bool_val(s6) +
                 bool_val(s7) +
                 bool_val(s8) +
                 bool_val(s9) +
                 bool_val(s10) +
                 bool_val(s11) == 5))

    # 8. Exactly one of statements 3 and 10 is false.
    s.add(s8 == z3.Xor(s3, s10))

    # 9. Exactly one of statements 6 and 10 is true.
    s.add(s9 == z3.Xor(s6, s10))

    # 10. Exactly one of statements 1 and 2 is false.
    s.add(s10 == z3.Xor(s1, s2))

    # 11. Statements 1, 8 and 11 are all false.
    s.add(s11 == z3.And(z3.Not(s1), z3.Not(s8), z3.Not(s11)))

    while s.check() == z3.sat:
        m = s.model()
        print("cat alive?", m.eval(cat_alive))
        print("s1: ", m.eval(s1))
        print("s2: ", m.eval(s2))
        print("s3: ", m.eval(s3))
        print("s4: ", m.eval(s4))
        print("s5: ", m.eval(s5))
        print("s6: ", m.eval(s6))
        print("s7: ", m.eval(s7))
        print("s8: ", m.eval(s8))
        print("s9: ", m.eval(s9))
        print("s10: ", m.eval(s10))
        print("s11: ", m.eval(s11))

        # Any more models?
        answer = z3.And(
            s1 == m.eval(s1),
            s2 == m.eval(s2),
            s3 == m.eval(s3),
            s4 == m.eval(s4),
            s5 == m.eval(s5),
            s6 == m.eval(s6),
            s7 == m.eval(s7),
            s8 == m.eval(s8),
            s9 == m.eval(s9),
            s10 == m.eval(s10),
            s11 == m.eval(s11),
        )
        s.add(z3.Not(answer))
        print()



if __name__ == "__main__":
    main()


"""
Is Schrödinger’s cat alive or dead?

1. Schrödinger’s cat is alive.
2. Schrödinger’s cat is dead.
3. Exactly one of statements 6 and 9 is true.
4. Exactly one of statements 2 and 6 is false.
5. Statements 4, 5 and 10 are all false.
6. Exactly one of statements 1 and 10 is false.
7. Exactly 5 statements are true.
8. Exactly one of statements 3 and 10 is false.
9. Exactly one of statements 6 and 10 is true.
10. Exactly one of statements 1 and 2 is false.
11. Statements 1, 8 and 11 are all false.

1 = -2
2 = F
3 = T
4 = F
5 = F
6 = F
8 = F
9 = T
10 = T
11 = F
T = (1 | F)
1 = T

"""
