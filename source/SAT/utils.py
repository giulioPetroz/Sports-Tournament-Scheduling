"""
    Natural number generator.
"""
def gen_var_id():
    i = 0
    while True:
        i += 1
        yield i