'''
An object class for a value of a parameter.
'''


class Value:
    def __init__(self, p, v):
        self.param_name = p
        self.value = v
        self.visited = False
        self.visited_num = 0
