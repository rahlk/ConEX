from abc import ABCMeta, abstractmethod

class AbstractAlgo:
    __metaclass__ = ABCMeta

    @abstractmethod
    def run(self):
        raise NotImplementedError()
