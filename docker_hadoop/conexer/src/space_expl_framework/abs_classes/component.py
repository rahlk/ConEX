from abc import ABCMeta, abstractmethod

class AbsComponents:
    __metaclass__ = ABCMeta

    @abstractmethod
    def define_components(self, comp_list):
        raise NotImplementedError()
