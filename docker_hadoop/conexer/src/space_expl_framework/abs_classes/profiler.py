from abc import ABCMeta, abstractmethod

class AbstractProfiler:
    __metaclass__ = ABCMeta

    @abstractmethod
    def profile(self, conf):
        raise NotImplementedError()
