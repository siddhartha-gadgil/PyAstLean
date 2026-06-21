# PastaLeanCHECK START
# TARGET: command
# CHECK: Libraries.scipy.pyScipyFactorial (5 : Int)
# CHECK: Libraries.scipy.pyScipyComb (6 : Int) (2 : Int)
# CHECK: Libraries.scipy.pyScipyGamma
# CHECK: Libraries.scipy.pyScipyPi
# CHECK: Libraries.scipy.pyScipyGmean
# CHECK: Libraries.scipy.pyScipyDet
# CHECK: Libraries.scipy.pyScipyNorm
# CHECK-NOT: import Scipy
# PastaLeanCHECK END
from scipy.special import comb, factorial, gamma
from scipy import constants
from scipy.stats import gmean
from scipy.linalg import det, norm


def demo():
    a = factorial(5)
    b = comb(6, 2)
    g = gamma(5.0)
    p = constants.pi
    m = gmean([1.0, 4.0, 16.0])
    d = det([[1.0, 2.0], [3.0, 4.0]])
    n = norm([3.0, 4.0])
    return a
