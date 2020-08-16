import itertools
import sys


def parse(s):
    """ Parse something of the form n / m - a, b, c"""
    s = s.replace(" ", "")
    [d, s] = s.split("/")
    [n, *r] = s.split("-")
    if len(r) > 0:
        r = r[0].split(",")

    return int(d), int(n), {int(m) for m in r}


def killer():
    total, count, without = parse(" ".join(sys.argv[1:]))
    print(total, count, without)
    for i in itertools.combinations(set(range(1, 10)) - without, count):
        if sum(i) == total:
            print(i)


if __name__ == "__main__":
    print(parse("15 / 4 - 8 , 3"))
    print(parse("15 / 4"))
