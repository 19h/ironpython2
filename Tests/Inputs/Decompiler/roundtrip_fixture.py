"""Known-source fixture for the cached IronPython inverse compiler."""

from __future__ import division

import os
import sys as system
from collections import defaultdict, namedtuple as nt

CONSTANT = 7


def expressions(a, b=2, *args, **kwargs):
    local = None
    truth = True
    falsity = False
    integer = 42
    long_integer = 12345678901234567890L
    floating = 1.25
    complex_number = 2j
    text = "text"
    unicode_text = u"unicode"
    items = [a, b, integer]
    pair = (a, b)
    mapping = {"a": a, "b": b}
    unique = {a, b}
    sliced = items[1:-1:2]
    items[0] = a + b
    items[1:2] = [b]
    mapping["c"] = a
    a += 1
    b -= 1
    value = (-a + +b) * (a - b) / 2 // 3 % 4 ** 2
    bits = (a << 2) | (b >> 1) ^ (a & b)
    compared = a < b <= integer and a != b or a is None
    reverse = a not in items or a is not b
    called = os.path.join(text, unicode_text)
    dynamic = called.upper().strip("X")
    expanded = max(a, b, *args, **kwargs)
    conditional = a if truth else b
    delete_me = [1, 2, 3]
    del delete_me[0]
    return (local, falsity, long_integer, floating, complex_number, pair,
            mapping, unique, sliced, value, bits, compared, reverse, dynamic,
            expanded, conditional)


def branches(value):
    if value < 0:
        return "negative"
    elif value == 0:
        return "zero"
    else:
        result = []
    while value:
        value -= 1
        if value == 3:
            continue
        if value == 1:
            break
        result.append(value)
    else:
        result.append("done")
    return result


def loops(sequence):
    result = []
    for index, item in enumerate(sequence):
        result.append((index, item))
    else:
        result.append(None)
    return result


def exceptions(value):
    try:
        if value:
            raise ValueError("bad", value)
    except (ValueError, TypeError) as error:
        message = str(error)
    except Exception:
        raise
    else:
        message = "ok"
    finally:
        value = None
    return message


def closure(seed):
    state = [seed]

    def inner(delta=1):
        state[0] += delta
        return state[0]

    return inner


def generator(limit):
    for index in xrange(limit):
        received = yield index * 2
        if received is not None:
            yield received


def comprehensions(values):
    list_value = [item * 2 for item in values if item > 0]
    dict_value = {item: item * 2 for item in values if item > 0}
    set_value = {item * 2 for item in values if item > 0}
    generator_value = (item * 2 for item in values if item > 0)
    return list_value, dict_value, set_value, generator_value


def decorator(function):
    return function


@decorator
class Sample(object):
    """Fixture class."""

    class_value = CONSTANT

    def __init__(self, value):
        self.value = value

    @property
    def doubled(self):
        return self.value * 2

    @staticmethod
    def identity(value):
        return value


anonymous = lambda value: value + 1
