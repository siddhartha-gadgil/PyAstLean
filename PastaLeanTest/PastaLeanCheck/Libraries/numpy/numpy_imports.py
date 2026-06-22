# PastaLeanCHECK START
# TARGET: command
# CHECK: def array_demo := fun xs ↦ Libraries.numpy.pyNumpyArray xs
# CHECK: def asarray_demo := fun xs ↦ Libraries.numpy.pyNumpyArray xs
# CHECK: def zeros_demo := fun r ↦ fun c ↦ Libraries.numpy.pyNumpyZeros r c
# CHECK: def ones_demo := fun r ↦ fun c ↦ Libraries.numpy.pyNumpyOnes r c
# CHECK: def eye_demo := fun n ↦ Libraries.numpy.pyNumpyEye n
# CHECK: def identity_demo := fun n ↦ Libraries.numpy.pyNumpyEye n
# CHECK: def transpose_demo := fun xs ↦ Libraries.numpy.pyNumpyTranspose xs
# CHECK: def add_demo := fun xs ↦ fun ys ↦ Libraries.numpy.pyNumpyAdd xs ys
# CHECK: def subtract_demo := fun xs ↦ fun ys ↦ Libraries.numpy.pyNumpySubtract xs ys
# CHECK: def multiply_demo := fun xs ↦ fun ys ↦ Libraries.numpy.pyNumpyMultiply xs ys
# CHECK: def scale_demo := fun s ↦ fun xs ↦ Libraries.numpy.pyNumpyScale s xs
# CHECK: def dot_demo := fun xs ↦ fun ys ↦ Libraries.numpy.pyNumpyDot xs ys
# CHECK: def matmul_demo := fun xs ↦ fun ys ↦ Libraries.numpy.pyNumpyMatmul xs ys
# CHECK: def sum_demo := fun xs ↦ Libraries.numpy.pyNumpySum xs
# CHECK: def mean_demo := fun xs ↦ Libraries.numpy.pyNumpyMean xs
# CHECK: def trace_demo := fun xs ↦ Libraries.numpy.pyNumpyTrace xs
# CHECK: def flatten_demo := fun xs ↦ Libraries.numpy.pyNumpyFlatten xs
# PastaLeanCHECK END

import numpy as np


def array_demo(xs):
    return np.array(xs)


def asarray_demo(xs):
    return np.asarray(xs)


def zeros_demo(r, c):
    return np.zeros((r, c))


def ones_demo(r, c):
    return np.ones((r, c))


def eye_demo(n):
    return np.eye(n)


def identity_demo(n):
    return np.identity(n)


def transpose_demo(xs):
    return np.transpose(xs)


def add_demo(xs, ys):
    return np.add(xs, ys)


def subtract_demo(xs, ys):
    return np.subtract(xs, ys)


def multiply_demo(xs, ys):
    return np.multiply(xs, ys)


def scale_demo(s, xs):
    return np.scale(s, xs)


def dot_demo(xs, ys):
    return np.dot(xs, ys)


def matmul_demo(xs, ys):
    return np.matmul(xs, ys)


def sum_demo(xs):
    return np.sum(xs)


def mean_demo(xs):
    return np.mean(xs)


def trace_demo(xs):
    return np.trace(xs)


def flatten_demo(xs):
    return np.flatten(xs)
