from abc import ABCMeta, abstractmethod

class AbsConfSpace:
    __metaclass__ = ABCMeta

    @abstractmethod
    def read_confspace(self):
        raise NotImplementedError()

    @abstractmethod
    def get_all_params(self):
        raise NotImplementedError()

    @abstractmethod
    def get_default_conf(self):
        raise NotImplementedError()
