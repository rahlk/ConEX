'''
This script utilizes a trained performance model to predict the performance of a given configuration.
'''
# import os
import pandas as pd
# from sklearn.ensemble import RandomForestRegressor
# from sklearn import preprocessing
from sysconf import cfg
import pickle
import numpy as np
import csv

class PerfPredict:
    def __init__(self):
        self.pred_model = self.load_model()
        self.X_scaler = self.load_X_scaler()
        self.y_scaler = self.load_y_scaler()
        self.independent_params = self.load_independent_params()
        self.old_new_params = self.load_old_new_param_mapping()
        self.important_feature_from_model = self.load_important_feature_from_model()
        self.last_conf = None
        self.load_hadoop_params()
        self.hadoop_param_values = self.load_hadoop_param_values()

    def load_hadoop_params(self):
        hadoop_params = pd.read_excel(cfg.hadoop_params, header=0)
        # read feature names and their types
        # iterate rows
        self.cat_params = set()
        self.bool_params = set()
        self.str_params = set()
        for index, row in hadoop_params.iterrows():
            p_name = row['name'].lower().strip()
            p_type = row['type'].lower().strip()
            if 'category' == p_type:
                self.cat_params.add(p_name)
            if 'bool' in p_type:
                self.bool_params.add(p_name)
            if 'string' in p_type:
                self.str_params.add(p_name)

    def load_hadoop_param_values(self):
        # read parameter value in
        param_value_df = pd.read_excel(cfg.p_values, header=0)
        param_value = {}
        for index, row in param_value_df.iterrows():
            p_name = row['Parameters'].lower().strip()
            p_default = str(row['Default']).lower().strip()
            p_alter = str(row['Alternative']).lower().strip()
            p_alter = p_alter.split(',')
            p_alter = [v.lower().strip() for v in p_alter]
            p_alter.append(p_default)
            param_value[p_name] = p_alter
        return param_value

    def load_model(self):
        saved_model = pickle.load(open(cfg.perf_predict_model, 'rb'))
        return saved_model

    def load_X_scaler(self):
        X_scaler = pickle.load(open(cfg.X_scaler, 'rb'))
        # print X_scaler.mean_
        return X_scaler

    def load_y_scaler(self):
        y_scaler = pickle.load(open(cfg.y_scaler, 'rb'))
        # print y_scaler.mean_
        return y_scaler

    def load_independent_params(self):
        variables = []
        with open(cfg.conf_params, 'r') as fp:
            for line in fp:
                variables.append(line.strip())
        return variables

    def load_important_feature_from_model(self):
        variables = []
        with open(cfg.important_feature_from_model, 'r') as fp:
            for line in fp:
                variables.append(line.strip())
        return variables

    def load_old_new_param_mapping(self):
        '''
        Some parameters have been renamed in newer version of Hadoop.
        This function loads the mapping information (old->new) from a CSV file
        '''
        old_new = {}  # old_params -> new_params
        with open(cfg.old_new_param_mapping, 'rb') as csvfp:
            csvreader = csv.reader(csvfp, delimiter=',')
            for row in csvreader:
                old_new[row[0]] = row[1]
        return old_new

    def predict(self, in_conf, imp_params):
        '''
        Given a configuration, we predict its performance.
        :param conf:
        :return:
        '''
        # The input is a dictionary. We need to create a dataframe first.
        # copy conf as a new dictionary
        conf = in_conf.copy()
        conf = self.clean_conf(conf)
        conf_df = pd.DataFrame(conf)
        conf_df = self.clean_by_hadoop_parameters(conf_df)
        conf_df = conf_df.astype(float)
        param_to_print = set(imp_params)
        param_to_print = list(param_to_print.intersection(set(conf_df.columns.tolist())))
        # print conf_df[param_to_print].iloc[0]
        # print conf_df.to_dict()
        # print the difference between scaler parameters and given parameters
        # print self.scaler.
        scaled_conf = self.X_scaler.transform(conf_df)
        # print scaled_conf[0]
        # print scaled_conf
        predicted = self.pred_model.predict(scaled_conf)[0]
        predicted = np.array([predicted])
        predicted = predicted.reshape(-1, 1)
        predicted = self.y_scaler.inverse_transform(predicted)
        # print 'predicted performance: ', predicted[0][0]
        return predicted[0][0]

    def clean_conf(self, conf):
        '''
        This function cleans a given configuraiton so that it can be used as the input of the scaler and predictor.
        :return:
        '''
        new_conf = {}
        for index, p in enumerate(self.independent_params):
            if p not in conf:
                all_values = self.hadoop_param_values.get(p)
                conf[p] = all_values[-1]
                # conf[p] = self.X_scaler.mean_[index]
        for key in conf:
            if key in self.independent_params:
                new_conf[key] = [conf.get(key)]
        return new_conf

    def clean_by_hadoop_parameters(self, df):
        '''
        This function transfer the data by their types.
        :param df:
        :return:
        '''
        for col in df:
            # print col
            col_orig = col
            col = col.lower().strip()
            # drop meaningless string parameters except java opts
            if col in self.str_params and 'opts' not in col:
                # drop this column
                df.drop(col, axis=1, inplace=True)
                continue
            values = df[col_orig]
            if col in self.cat_params:
                # replace values with their indes
                cat_values = self.hadoop_param_values[col]
                values = [cat_values.index(str(v).lower().strip()) + 1 for v in values]
                values = [float(v) for v in values]
                df[col_orig] = values
            elif col in self.bool_params:
                values = [str(v).lower().strip() for v in values]
                values = [True if v == 'true' else False for v in values]
                values = [float(v)+1 for v in values]
                df[col_orig] = values
            elif 'opts' in col:
                # here we remove alpha characters in -Xmx200m
                values = [float(v[4:-1]) for v in values]
                df[col_orig] = values
            else:
                values = [float(v) for v in values]
                df[col_orig] = values
        return df

    def special_conf_preprocessing(self, df):
        # df = self.special_str_to_scaler(df)
        # df = self.special_remove_str_features(df)
        # df = self.special_set_correct_maps(df)
        # df = self.decompose_features(df)
        return df

    def special_str_to_scaler(self, df):
        '''
        This function will replace all string features with their group index
        Possible problem:
            The string feature is checked with 'np.object'. If there are other
            types of features that are treated by Pandas as np.object. Those
            features will be replaced too.

        We could use checksum too. But using checksum could lead to losing a lot
        information.
        '''
        mapred_input_dir = 'mapred.input.dir'
        if self.old_new_params.get(mapred_input_dir) is not None:
            mapred_input_dir = self.old_new_params.get(mapred_input_dir)
        for col in df.columns:
            # split input data by comma, this cannot be applied to hitchcock data
            # if col == mapred_input_dir:
            #     dirs = df[col].astype(str)
            #     num_dirs = list(map(lambda x: len(x.split(',')), dirs))
            #     df[col] = np.array(num_dirs)
            # if ('hive.query.' not in col) and df[col].dtype == np.object:
            # do not apply this on hive.query.string
            if df[col].dtype == np.object:
                # group values first and then replace values with their group index
                # transfrom a column to category type
                values = df[col].astype('category')
                # get the codes of a category type, and add 1 to each index, to
                # transfrom index 0 to 1
                group_idx = values.cat.codes.apply(lambda x: x + 1)
                # give the group index back to df
                df[col] = group_idx
        return df

    def special_remove_str_features(self, df):
        new_df = pd.DataFrame()
        for col in df.columns:
            # The dtype of string features will be 'str', which we have dealed with
            # filter out the left 'str' features if there is any
            if col.lower() == 'job_id' or \
                    str(df[col].dtype).startswith('bool') or \
                    str(df[col].dtype).startswith('int') or \
                    str(df[col].dtype).startswith('float'):
                new_df[col] = df[col]
        return new_df

    def special_set_correct_maps(self, df):
        '''
        The expression to compute the number of map tasks is:
        max(mapred.min.split.size, min(mapred.max.split.size, dfs.block.size))

        Most of jobs don't have this parameter in the dataset, so we set a default
        value here.
        '''
        # set the default block size as 64M
        default_dfs_blocksize = 64 * 1024 * 1024
        default_max_split_size = 256000000  # about 244M
        default_min_split_size = 104857600  # 100M
        map_task_name = 'mapred.map.tasks'
        if self.old_new_params.get(map_task_name) is not None:
            map_task_name = self.old_new_params.get(map_task_name)
        map_task_name = 'mapreduce.job.maps'
        new_tasks = []
        maxsize_col_name = 'mapreduce.input.fileinputformat.split.maxsize'
        minsize_col_name = 'mapreduce.input.fileinputformat.split.minsize'
        if maxsize_col_name not in df.columns \
                or minsize_col_name not in df.columns:
            return df
        max_split_col = df[maxsize_col_name].values
        min_split_col = df[minsize_col_name].values
        for idx, min_split in enumerate(min_split_col):
            min_split = self.clean_split_size(min_split, default_min_split_size)
            max_split = self.clean_split_size(max_split_col[idx],
                                         default_max_split_size)
            map_task = max(min_split, min(max_split, default_dfs_blocksize))
            new_tasks.append(map_task)
        df[map_task_name] = new_tasks
        return (df)

    def clean_split_size(self, value, default_value):
        if np.isnan(value):
            value = default_value
        if int(value) <= 1:
            value = default_value
        return (value)

    def decompose_features(self, df):
        '''
        This 'helper' function calls previous defined three data clean function
        '''
        df = self.decomp_conditional_features(df)
        df = self.remove_negative_feature(df)
        # df = self.remove_non_dot_feature(df)
        df = self.transform_java_opts(df)
        # write_to_excel(df, 'after_decompose.xlsx')
        return df

    def transform_java_opts(self, df):
        # java_opts like -Xmx4g will be evalueated to MB
        java_opts = [opt for opt in df.columns if opt.strip().endswith('.opts')]
        for col_name in java_opts:
            col_values = df[col_name].values.ravel()
            for idx, v in enumerate(col_values):
                v = str(v).strip().lower()
                # the value could be something like '-Xmx4g'
                # otherwise, set the value as 0
                if '-xmx' not in v:
                    col_values[idx] = 0
                    continue
                opts = v.split(' ')
                # find '-xmx' part
                for opt in opts:
                    if '-xmx' not in opt:
                        continue
                    size = opt.split('-xmx')[-1]
                    # get the number part, like 4 or 12
                    int_size = size[0:-1]
                    # size[-1] is 'g', we need to transfer to MB
                    if size[-1] is 'g':
                        int_size = int_size * 1024
                    col_values[idx] = int_size
            df[col_name] = col_values
        return (df)

    def decomp_conditional_features(self, df):
        '''
        In a group of conditional features, when the primary key is False or 0, the
        other features in the same group should be removed/set to 0.
        '''
        conditional_features = {
            'cascading.flow.executing': ['cascading.flow.id',
                                         'cascading.flow.planner',
                                         'cascading.flow.platform',
                                         'cascading.flow.registry',
                                         'cascading.flow.step',
                                         'cascading.flow.step.id',
                                         'cascading.flow.step.node.map.path',
                                         'cascading.flow.step.node.reduce.path',
                                         'cascading.flow.step.num',
                                         'cascading.flow.tuple.element.comparator'
                                         ],
            'datanucleus.cache.level2': ['datanucleus.cache.level2.type'],
            'fs.s3a.multipart.purge': ['fs.s3a.multipart.purge.age',
                                       'fs.s3a.multipart.size',
                                       'fs.s3a.multipart.threshold'],
            'fs.s3n.multipart.uploads.enabled':
                ['fs.s3n.multipart.copy.block.size',
                 'fs.s3n.multipart.uploads.block.size'],
            'hadoop.ssl.enabled': ['hadoop.ssl.enabled.protocols',
                                   'hadoop.ssl.exclude.cipher.suites',
                                   'hadoop.ssl.exclude.insecure.protocols',
                                   'hadoop.ssl.hostname.verifier',
                                   'hadoop.ssl.keystores.factory.class',
                                   'hadoop.ssl.require.client.cert',
                                   'hadoop.ssl.server.conf'],
            'hive.auto.convert.join':
                ['hive.auto.convert.join.noconditionaltask',
                 'hive.auto.convert.join.noconditionaltask.size',
                 'hive.auto.convert.join.use.nonstaged'],
            'hive.auto.convert.sortmerge.join':
                ['hive.auto.convert.sortmerge.join.bigtable.selection.policy',
                 'hive.auto.convert.sortmerge.join.nonconditionaltask',
                 'hive.auto.convert.sortmerge.join.to.mapjoin'],
            'hive.exec.infer.bucket.sort':
                ['hive.exec.infer.bucket.sort.num.buckets.power.two'],
            'hive.exec.mode.local.auto':
                ['hive.exec.mode.local.auto.input.files.max',
                 'hive.exec.mode.local.auto.inputbytes.max'],
            'hive.exec.parallel': ['hive.exec.parallel.thread.number'],
            'hive.limit.optimize.enable':
                ['hive.limit.optimize.fetch.max',
                 'hive.limit.optimize.limit.file'],
            'hive.map.aggr': ['hive.map.aggr.hash.force.flush.memory.threshold',
                              'hive.map.aggr.hash.min.reduction',
                              'hive.map.aggr.hash.percentmemory'],
            'hive.map.groupby.sorted': ['hive.map.groupby.sorted.testmode'],
            'hive.merge.current.job.concatenate.list.bucketing':
                ['hive.merge.current.job.concatenate.list.bucketing.depth'],
            'hive.metastore.try.direct.sql': ['hive.metastore.try.direct.sql.ddl'],
            'hive.optimize.bucketmapjoin':
                ['hive.optimize.bucketmapjoin.sortedmerge'],
            'hive.optimize.index.filter':
                ['hive.optimize.index.filter.compact.maxsize',
                 'hive.optimize.index.filter.compact.minsize'],
            'hive.optimize.ppd': ['hive.optimize.ppd.storage'],
            'hive.optimize.reducededuplication':
                ['hive.optimize.reducededuplication.min.reducer'],
            'hive.optimize.sampling.orderby':
                ['hive.optimize.sampling.orderby.number',
                 'hive.optimize.sampling.orderby.percent'],
            'hive.optimize.skewjoin': ['hive.optimize.skewjoin.compiletime'],
            'hive.prewarm.enabled': ['hive.prewarm.numcontainers'],
            'hive.security.authorization.enabled':
                ['hive.security.authorization.manager'],
            'hive.test.mode': ['hive.test.mode.prefix',
                               'hive.test.mode.samplefreq'],
            'hive.variable.substitute': ['hive.variable.substitute.depth'],
            'hive.vectorized.execution.enabled':
                ['hive.vectorized.execution.reduce.enabled'],
            'job.end.retry.attempts': ['job.end.retry.interval'],
            'mapred.output.compress': ['mapred.output.compression.codec',
                                       'mapred.output.compression.type'],
            'mapred.task.profile': ['mapred.task.profile.maps',
                                    'mapred.task.profile.reduces'],
            'output.compression.enabled': ['output.compression.codec'],
            'hive.exec.compress.intermediate': ['mapred.output.compress.*'],
            'hive.exec.dynamic.partition':
                ['hive.exec.dynamic.partition.mode',
                 'hive.exec.max.dynamic.partitions',
                 'hive.exec.max.dynamic.partitions.pernode'],
            'mapred.task.calculate.resource.usage':
                ['mapreduce.tasktracker.resourcecalculatorplugin']}

        for p_key, features in conditional_features.items():
            # replace deprecated parameters with new ones
            ###########################
            new_p_key = self.old_new_params.get(p_key)
            if new_p_key is not None:
                p_key = new_p_key
            new_features = []
            for f in features:
                tmp_feature = self.old_new_params.get(f)
                if tmp_feature is not None:
                    new_features.append(tmp_feature)
                else:
                    new_features.append(f)
            features = new_features
            ###########################

            if p_key not in df.columns:
                continue
            p_key_values = df[p_key].values.ravel()
            # some feature might not be in the data set
            existing_features = [f for f in features if f in df.columns]

            # ############# Debug ###################
            # for f in existing_features:
            #     print 'decompose features: ', f
            # ############# Debug ###################

            # feature_values is a two dimension array
            feature_values = []
            for f in existing_features:
                feature_values.append(df[f].values.ravel())

            for idx, pv in enumerate(p_key_values):
                if np.isnan(pv) or int(pv) != 0:
                    continue
                for i in range(len(feature_values)):
                    feature_values[i][idx] = 0

            for idx, f in enumerate(existing_features):
                df[f] = feature_values[idx]
        return (df)

    def remove_negative_feature(self, df):
        '''
        Some features with value -1 means that no limit on these feature. So they
        don't control anything. In this case, we can set them as 0/remove
        these feature.
        '''
        remove_if_negative_one = ['mapred.cluster.map.memory.mb',
                                  'mapred.cluster.max.map.memory.mb',
                                  'mapred.cluster.max.reduce.memory.mb',
                                  'mapred.cluster.reduce.memory.mb',
                                  'mapred.job.reduce.memory.mb',
                                  'mapred.job.map.memory.mb',
                                  'mapred.job.reuse.jvm.num.tasks',
                                  'mapred.jobtracker.maxtasks.per.job',
                                  'mapreduce.cluster.map.userlog.retain-size',
                                  'mapreduce.cluster.reduce.userlog.retain-size',
                                  'mapreduce.reduce.input.limit',
                                  'hive.cli.pretty.output.num.cols',
                                  'hive.fetch.task.conversion.threshold',
                                  'hive.limit.pushdown.memory.usage',
                                  'hive.limit.query.max.table.partition',
                                  'hive.optimize.index.filter.compact.maxsize',
                                  'hive.tez.container.size',
                                  'kafka.max.pull.hrs',
                                  'kafka.max.pull.minutes.per.task',
                                  'pig.info.reducers.default.parallel',
                                  'pig.info.reducers.estimated.parallel']
        # replace deprecated parameters with new ones
        ###########################
        remove_if_negative_one = [self.old_new_params.get(f)
                                  if self.old_new_params.get(f) is not None
                                  else f for f in remove_if_negative_one]
        ###########################
        for col in remove_if_negative_one:
            if col not in df.columns:
                continue
            # print 'default_value feature: ', col
            values = df[col]
            only_negative = [0 if x == -1 else x for x in values]
            df[col] = only_negative
        return df