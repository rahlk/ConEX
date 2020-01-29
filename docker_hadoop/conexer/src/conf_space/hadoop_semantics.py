import json
from sysconf import cfg

class HadoopSemantics:
    def __init__(self):
        # read parameter hierarchical structure
        with open(cfg.hadoop_param_hierarchy) as fp:
            # this is a python dictionary
            self.hierarchy_structure = json.load(fp)

    def get_all_parents(self):
        return self.hierarchy_structure.keys()

    def get_children_by_parent(self, parent):
        return self.hierarchy_structure[parent]

    def get_partial_structure(self, params):
        '''
        The input is a list of parameters.
        This function will check whether there is hierarchical structure
        exist in this list.

        If exists, this function will create a subset hierarchical structure.
        Otherwise, this function will return an empty dictionary.

        Return: A subset of structure. The keys and values are all
                in input params.
        '''
        ret = dict()
        for p in params:
            if p not in self.hierarchy_structure:
                continue
            children_params = self.hierarchy_structure[p]
            children_in_inputs = list(set(params).intersection(set(children_params)))
            ret[p] = children_params
        # print 'HadoopSemantics==get_partial_structure, length of subset', len(ret)
        return ret

    def get_parent(self, params):
        '''
        This function gets the parent of children in input params.
        Ignore params who have no parent.
        '''
        ret = dict()
        for parent, children in self.hierarchy_structure.iteritems():
            children_in_params = [p for p in params if p in children]
            for c in children_in_params:
                ret[c] = parent
        # there are some parameters have no parent
        # this is totally OK
        # print 'HadoopSemantics=get_parent, length of c->p:', len(ret)
        return ret

    def remove_dup_confs(self, confs):
        '''
        Given a list of configurations, this function remove duplicates by
        semantics. The confs are a list of dictionaries where a key is a
        parameter and corresponding value is the value of that parameter.

        Now, we have only hierarchical structure.
        '''
        print 'HadoopSemantics=remove_dup_confs, input #confs:', len(confs)
        all_params_from_confs = confs[0].keys()
        all_parents = self.hierarchy_structure.keys()
        all_parents = [p.lower() for p in all_parents]
        parent_params = [p for p in all_params_from_confs if p in all_parents]
        children_parent = self.get_parent(all_params_from_confs)
        print 'HadoopSemantics=remove_dup_confs, #children:', children_parent.keys()
        normal_params = set(all_params_from_confs).copy()
        # normal_params.difference_update(set(parent_params))
        normal_params.difference_update(set(children_parent.keys()))
        # normal_params = list(normal_params)
        params_to_compare = list(normal_params.copy())
        print 'HadoopSemantics=remove_dup_confs, #parent parameters:', parent_params
        uniq_confs = []
        conf_index_to_remove = set()
        total_confs = len(confs)
        for i in range(0, total_confs-1):
            confi = confs[i]
            for j in range(i+1, total_confs):
                confj = confs[j]
                all_param_same = True
                for p in params_to_compare:
                    vi = str(confi[p])
                    vj = str(confj[p])
                    # if p is parent parameters
                    if vi != vj:
                        all_param_same = False
                        break
                    # although two values are same
                    # however, if the parameter is a parent and the value is
                    # 'false', we still think they are same no matter what
                    # value children parameters have
                    if p in parent_params and vi == 'false': # and vj == 'false'):
                        all_param_same = False
                        break
                if all_param_same:
                    # only remove one of them
                    conf_index_to_remove.add(j)
        print 'HadoopSemantics=remove_dup_confs, #index_to_remove:', len(conf_index_to_remove), '===', conf_index_to_remove
        for i, conf in enumerate(confs):
            if i in conf_index_to_remove:
                continue
            uniq_confs.append(conf)
        print 'HadoopSemantics=remove_dup_confs, return #confs:', len(uniq_confs)
        return uniq_confs
