import pandas as pd
from sysconf import cfg
import math


class HistData:
    def __init__(self):
        self.hist_data = self.read_hist_data()
        self.N, self.conf_index, self.distances = self.read_dist_matrix()
        self.visited = set()

    def read_dist_matrix(self):
        with open(cfg.distance, 'r') as fp:
            lines = fp.read().splitlines()
            N = int(lines[0])
            conf_index = lines[1].split(',')
            distances = [float(d) for d in lines[2:]]
            return N, conf_index, distances

    def read_hist_data(self):
        hist_df = pd.read_excel(cfg.hist_data, header=0)
        hist_df.sort_values('performance', axis='rows', inplace=True)
        return hist_df

    def condensed_to_square_idx(self, k):
        n = self.N
        # i = calc_row_idx(k, n)
        # calculate row index
        i = int(math.ceil((1/2.) * (- (-8*k + 4 *n**2 -4*n - 7)**0.5 + 2*n -1) - 1))
        # calculate column index
        # j = calc_col_idx(k, i, n)
        j = int(n - (i * (n - 1 - i) + (i * (i + 1)) / 2) + k)
        return i, j

    def square_idx_to_condensed(self, i, j):
        assert i != j, "no diagonal elements in condensed matrix"
        n = self.N
        if i < j:
            i, j = j, i
        return n*j - j*(j+1)/2 + i - 1 - j

    def get_next_neighbor_by_dist(self, curr_idx):
        # get the distance among all neighbors
        # curr_idx is the job_id. Convert it to index in the list of all indexes
        self.visited.add(curr_idx)
        if curr_idx not in self.conf_index:
            print 'cannot find index "', curr_idx, '" in the history data. Return...'
            return None, None
        num_idx = self.conf_index.index(curr_idx)
        # print 'Current index:', curr_idx
        nearest_index = None
        nearest_dist = 100000   # define a large integer as the initial distance
        for i in range(self.N):
            if i == num_idx or self.conf_index[i] in self.visited:
                continue
            condensed_index = self.square_idx_to_condensed(i, num_idx)
            # print 'condensed index:', condensed_index
            tmp_distance = self.distances[condensed_index]
            if tmp_distance < nearest_dist:
                nearest_dist = tmp_distance
                nearest_index = self.conf_index[i]
        # got the nearest neighbor and return its configuration
        self.visited.add(nearest_index)
        return nearest_index, self.hist_data.loc[nearest_index].to_dict()
