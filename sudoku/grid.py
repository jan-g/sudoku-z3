from z3 import z3


class Grid:
    def __init__(self, *content, x=9, y=9, dx=3, dy=3):
        if len(content) > 0:
            x = len(content(0))
            y = len(content)
        self.solver = z3.Solver()
        self.x = x
        self.y = y
        self.dx = dx
        self.dy = dy
        self.cells = {(i, j) for j in range(y) for i in range(x)}
        self.vars = {}
        self.construct_grid()
        self.apply_constraints(*content)

    def __getitem__(self, c):
        k = c
        try:
            (x, y) = c
            k = "c{}-{}".format(x, y)
        except ValueError:
            pass
        if k not in self.vars:
            self.vars[k] = z3.Int(k)
        return self.vars[k]

    def add(self, constraint):
        self.solver.add(constraint)

    def apply_constraints(self, *content):
        for j in range(len(content)):
            line = content[j].replace(" ", "")
            for i in range(len(line)):
                try:
                    self.set(i, j, int(line[i]))
                except ValueError:
                    pass

    def construct_grid(self):
        for (x, y) in self.cells:
            v = self[x, y]
            self.add(1 <= v)
            self.add(v <= self.x)

    def row_of(self, c):
        (x, y) = c
        return self.row(y)

    def column_of(self, c):
        (x, y) = c
        return self.column(x)

    def row(self, y):
        return sorted((i, j) for (i, j) in self.cells if j == y)

    def column(self, x):
        return sorted((i, j) for (i, j) in self.cells if i == x)

    def box_of(self, c, dx=None, dy=None):
        """eg, box((1, 1), 3, 3) returns all members of the 3x3 box that 1, 1 fits in"""
        if dx is None:
            dx = self.dx
        if dy is None:
            dy = self.dy
        (x, y) = c
        bx = x // dx * dx
        by = y // dy * dy
        return {(x, y) for (x, y) in self.cells if bx <= x < bx + dx and by <= y < by + dy}

    def distinct(self, c1, c2):
        self.rel(lambda v1, v2: v1 != v2, c1, c2)

    def distinct_vars(self, vars):
        for i in range(len(vars) - 1):
            for j in range(i + 1, len(vars)):
                self.add(vars[i] != vars[j])

    def rel(self, r, c1, c2):
        """rel(v1, v2) should evaluate to the relationship"""
        if c1 == c2:
            return
        self.add(r(self[c1], self[c2]))

    def rel_all(self, r, c1, c2s):
        for c2 in c2s:
            self.rel(r, c1, c2)

    def distinct_all(self, c1, c2s):
        for c2 in c2s:
            self.distinct(c1, c2)

    def solve(self):
        sat = self.solver.check()
        assert sat == z3.sat
        m = self.solver.model()
        return {(x, y): m.eval(self[x, y]) for (x, y) in self.cells}

    def reject(self, solution):
        r = z3.And(*(self[x, y] == solution[x, y] for (x, y) in solution))
        n = z3.Not(r)
        self.add(n)

    def boxes_unique(self, dx=None, dy=None):
        for c in self.cells:
            self.distinct_all(c, self.box_of(c, dx=dx, dy=dy))

    def rows_unique(self):
        self.boxes_unique(dx=self.x, dy=1)

    def columns_unique(self):
        self.boxes_unique(dx=1, dy=self.y)

    def set(self, x, y, v):
        self.solver.add(self[x, y] == v)

    def diagonals(self, c):
        (x, y) = c
        return sorted((i, j) for (i, j) in self.cells if abs(x - i) == abs(y - j))

    def sandwich(self, bound1, bound2, total, cells):
        for i, c1 in enumerate(cells[:-1]):
            c1 = self[c1]
            sum = 0
            condition1 = z3.Or(c1 == bound1, c1 == bound2)
            for j, c2 in enumerate(cells[i + 1:]):
                c2 = self[c2]
                condition2 = z3.Or(c2 == bound1, c2 == bound2)
                self.add(z3.Implies(condition1, z3.Implies(condition2, sum == total)))
                sum += c2

    def killer(self, total, cells):
        self.distinct_vars([self[c] for c in cells])
        aggregate = sum(self[c] for c in cells)
        self.add(aggregate == total)

    def thermometer(self, sequence):
        for i in range(len(sequence) - 1):
            self.rel(lambda v1, v2: v1 < v2, sequence[i], sequence[i + 1])


def format(s):
    miny = min(y for (x, y) in s)
    maxy = max(y for (x, y) in s)
    minx = min(x for (x, y) in s)
    maxx = max(x for (x, y) in s)
    return "\n".join("".join(str(s[x, y]) for x in range(minx, maxx + 1)) for y in range(miny, maxy + 1))


def all_solutions(g):
    solution = g.solve()
    print(format(solution))

    print()
    print("checking for uniqueness")
    try:
        while True:
            g.reject(solution)
            solution = g.solve()
            print("another solution found")
            print(format(solution))
    except AssertionError:
        print("solution is unique")


def main():
    g = Grid()
    g.rows_unique()
    g.columns_unique()
    g.boxes_unique()
    forged_letters(g)
    all_solutions(g)


def simple_sandwich(g):
    g.apply_constraints(
        "... ... ...",
        "... ... ...",
        "..9 ... ...",

        "... 6.. ...",
        "... .1. ...",
        "... ..2 ...",

        "... ... 7..",
        "... ... ...",
        "... ... ...",
    )

    for row, total in enumerate((2, 8, 26, 29, 0, 23, 15, 2, 4)):
        g.sandwich(1, 9, total, g.row(row))

    for col, total in enumerate((10, 23, 23, 23, 14, 12, 21, 0, 0)):
        g.sandwich(1, 9, total, g.column(col))


# The following are taken from:
# A Sudoku Puzzle Hunt
# By Ben Needham

def lascivious_queens(g):
    g.apply_constraints(
        "9.. ... ..1",
        "... .9. 2..",
        "..7 .1. 9..",

        ".2. ... ...",
        "... ... ...",
        "5.. 4.3 .2.",

        "..5 ..1 8..",
        "... ... ...",
        "3.. ... ..5",
    )

    # Queen's constraint for anything >= 4
    for c in g.cells:
        g.rel_all(lambda v1, v2: z3.Or(v1 < 4, v1 != v2), c, g.diagonals(c))

    # "..3 6..",
    # ".2. ..4",
    #
    # "5.. .6.",
    # ".3. ..5",
    #
    # "3.. .1.",
    # "..1 4..",


def forged_letters(g):
    g.apply_constraints(
        "... ... ...",
        "... ... ...",
        "... ... ...",

        "195 .3. ...",
        "... ... ...",
        "... ... ...",

        "... ... ...",
        "..8 ... ...",
        "... .9. ...",
    )
    letters = [d, a, n, t, e, i, f, r, o] = [g[letter] for letter in "danteifro"]
    for letter in letters:
        g.add(1 <= letter)
        g.add(letter <= 9)

    # Make all of these variables distinct
    g.distinct_vars(letters)

    # Line up the letters on the grid
    g.add(i == g[1, 1])
    g.add(d == g[3, 1])
    g.add(a == g[4, 1])
    g.add(n == g[5, 1])
    g.add(t == g[6, 1])
    g.add(e == g[7, 1])

    # Add the sandwich clues
    g.sandwich(1, 9, o, g.row(0))
    g.sandwich(1, 9, d * 10 + r, g.row(4))
    g.sandwich(1, 9, a * 10 + t, g.row(6))
    g.sandwich(1, 9, o, g.row(8))

    g.sandwich(1, 9, d * 10 + e, g.column(4))
    g.sandwich(1, 9, a * 10 + r, g.column(5))

    # Add the killer grids
    killers = [line.replace(" ", "")
               for line in """
                    AAA AA. ...
                    ..B BB. ...
                    ..B BB. ...

                    ..B .C. D..
                    EE. ..C .D.
                    EEE ... ...

                    ... ... FFF
                    ... ... G.F
                    ... ... GGG
                """.splitlines() if line.strip() != ""]

    totals = {
        "A": d * 10 + o,
        "B": n * 10 + t,
        "C": f,
        "D": e,
        "E": a * 10 + r,
        "F": d * 10 + e,
        "G": a * 10 + d,
    }

    for region in totals:
        cells = [(x, y) for (y, line) in enumerate(killers) for (x, cell) in enumerate(line) if cell == region]
        g.killer(totals[region], cells)

    # Add the thermometers - which look vaguely like this:
    # ... ... ...
    # |.. ... ...
    # |.. |.. /..
    #
    # O.. \./ ...
    # ... .|. ...
    # ... .O. ...
    #
    # |.. ... ...
    # \.. ... ...
    # .O. ..O --.
    # (These turn out to be superfluous for the solution, technically.)

    g.thermometer([(0, 3), (0, 2), (0, 1)])
    g.thermometer([(1, 8), (0, 7), (0, 6)])
    g.thermometer([(5, 8), (6, 8), (7, 8)])
    g.thermometer([(4, 5), (4, 4), (3, 3), (3, 2)])
    g.thermometer([(4, 5), (4, 4), (5, 3), (6, 2)])


if __name__ == '__main__':
    main()
