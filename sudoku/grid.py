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

    def apply_constraints(self, *content):
        for j in range(len(content)):
            line = content[j].replace(" ", "")
            for i in range(len(line)):
                try:
                    self.set(i, j, int(line[i]))
                except ValueError:
                    pass

    def construct_grid(self):
        s = self.solver
        for (x, y) in self.cells:
            v = self.vars[x, y] = z3.Int("c{}-{}".format(x, y))
            s.add(1 <= v)
            s.add(v <= self.x)

    def row(self, c):
        (x, y) = c
        return self.row_all(y)

    def column(self, c):
        (x, y) = c
        return self.column_all(x)

    def row_all(self, y):
        return {(i, j) for (i, j) in self.cells if j == y}

    def column_all(self, x):
        return {(i, j) for (i, j) in self.cells if i == x}

    def box(self, c, dx=None, dy=None):
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

    def rel(self, r, c1, c2):
        """rel(v1, v2) should evaluate to the relationship"""
        if c1 == c2:
            return
        self.solver.add(r(self.vars[c1], self.vars[c2]))

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
        return {(x, y): m.eval(self.vars[x, y]) for (x, y) in self.cells}

    def reject(self, solution):
        r = z3.And(*(self.vars[x, y] == solution[x, y] for (x, y) in solution))
        n = z3.Not(r)
        self.solver.add(n)

    def boxes_unique(self, dx=None, dy=None):
        for c in self.cells:
            self.distinct_all(c, self.box(c, dx=dx, dy=dy))

    def rows_unique(self):
        self.boxes_unique(dx=self.x, dy=1)

    def columns_unique(self):
        self.boxes_unique(dx=1, dy=self.y)

    def set(self, x, y, v):
        self.solver.add(self.vars[x, y] == v)

    def diagonals(self, c):
        (x, y) = c
        return {(i, j) for (i, j) in self.cells if abs(x - i) == abs(y - j)}


def format(s):
    miny = min(y for (x, y) in s)
    maxy = max(y for (x, y) in s)
    minx = min(x for (x, y) in s)
    maxx = max(x for (x, y) in s)
    return "\n".join("".join(str(s[x, y]) for x in range(minx, maxx + 1)) for y in range(miny, maxy + 1))


def main():
    g = Grid()
    g.rows_unique()
    g.columns_unique()
    g.boxes_unique()
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


if __name__ == '__main__':
    main()
