"""Demonstration of Unsupported syntax or libraries (logging, requests, random) don't abort
the whole translation — those lines become `pyUnsupported(...)` placeholders that carry the
original Python source, and the rest of the program transpiles and runs normally.
"""

import logging

import requests

logger = logging.getLogger(__name__)


def total_score(scores: list[int]) -> int:
    logger.info("scoring")              # foreign -> placeholder
    blob = requests.get("http://x")     # foreign -> placeholder
    total = 0
    for s in scores:
        total = total + s               # real logic -> translated
    return total


def main():
    logging.basicConfig(level=logging.INFO)   # foreign -> placeholder
    scores = [10, 20, 30, 40]
    print("total", total_score(scores))
    print("doubled", total_score(scores) * 2)


if __name__ == "__main__":
    main()
