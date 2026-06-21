# PastaLeanCHECK START
# TARGET: command
# CHECK: def total := fun (xs : List Int)
# CHECK: def scale := fun (row : List Float)
# CHECK: def label := fun (pairs : Std.HashMap String Int)
# CHECK-NOT: import Typing
# PastaLeanCHECK END

from __future__ import annotations
from typing import Dict, List, Sequence


def total(xs: List[int]) -> int:
    s = 0
    for x in xs:
        s = s + x
    return s


def scale(row: Sequence[float], k: float) -> List[float]:
    out: List[float] = []
    for v in row:
        out.append(v * k)
    return out


def label(pairs: Dict[str, int], key: str) -> int:
    return pairs.get(key, 0)


def main():
    print("total", total([1, 2, 3, 4]))
    print("scaled", scale([1.0, 2.0], 3.0))


if __name__ == "__main__":
    main()
