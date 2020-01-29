#from hill_climbing import HillClimbing
#from mcmc import MCMC
from genetic import Genetic
from coordinate_descent import CoordinateDescent


class Searcher:
    def __init__(self):
        #self.hill_climbing = HillClimbing()
        #self.mcmc = MCMC()
        self.genetic = Genetic()
        self.coordinate_descent = CoordinateDescent()
        return None
