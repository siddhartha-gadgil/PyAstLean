# PastaLeanCHECK START
# TARGET: command
# EXIT: 1
# CHECK-ERR: Python while-else blocks are not supported.
# PastaLeanCHECK END
def fail_while_else():
    while True:
        pass
    else:
        pass
