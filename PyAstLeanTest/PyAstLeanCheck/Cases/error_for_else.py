# PYASTLEANCHECK START
# TARGET: command
# EXIT: 1
# CHECK-ERR: Python for-else blocks are not supported.
# PYASTLEANCHECK END
def fail_for_else():
    for i in range(10):
        pass
    else:
        pass
