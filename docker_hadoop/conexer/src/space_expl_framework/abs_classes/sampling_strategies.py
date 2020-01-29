from abc import ABCMeta, abstractmethod, abstractproperty

class AbstractSamplingStrategy:
    __metaclass__ = ABCMeta

    @abstractmethod
    def next_value(self):
        raise NotImplementedError()
