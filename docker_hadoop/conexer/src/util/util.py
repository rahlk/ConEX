import xml.etree.cElementTree as ET
from xml.dom import minidom
import os, shutil, sys
from sysconf import cfg
from conf_space import Parameter
import pandas as pd
from conf_space import ConfType, ConfDataType


def make_folder_ready(folder):
    # first delete possible files in the folder
    shutil.rmtree(folder, ignore_errors=True)
    # create a new folder
    os.makedirs(folder)


def get_datatype_by_str(dt_str):
    dt_str = dt_str.lower()
    if 'string' in dt_str:
        return ConfDataType.string
    elif 'bool' in dt_str:
        return ConfDataType.boolean
    elif 'int' in dt_str:
        return ConfDataType.integer
    elif 'float' in dt_str:
        return ConfDataType.float
    elif 'category' in dt_str:
        return ConfDataType.category
    else:
        return ConfDataType.unknown


def get_blongs_by_str(bstr):
    bstr = bstr.lower()
    if bstr == 'mapred':
        return ConfType.mapred
    elif bstr == 'core':
        return ConfType.core
    elif bstr == 'hdfs':
        return ConfType.hdfs
    elif bstr == 'yarn':
        return ConfType.yarn
    else:
        return ConfType.unknown

def read_parameter_importance():
    with open(cfg.important_params, 'r') as fp:
        lines = fp.readlines()
        lines = [l.strip() for l in lines if len(l) > 0]
        params =  [l.split(',')[0] for l in lines]
        params =  [p.strip() for p in params]
        strategies =  [l.split(',')[1] for l in lines]
        strategies = [s.strip() for s in strategies]
        param_sampling_strategy = {}
        for i, p in enumerate(params):
            param_sampling_strategy[p] = strategies[i]
        return params, param_sampling_strategy

important_params, param_sampling_strategy = read_parameter_importance()


def read_hadoop_params():
    parameters = {}
    hadoop_params = pd.read_excel(cfg.hadoop_params, header=0)
    p_name = hadoop_params['name']
    p_type = hadoop_params['type']
    p_belongs = hadoop_params['belongs']
    for idx, pt in p_type.iteritems():
        pname = p_name[idx] # .strip().lower()
        belongs = get_blongs_by_str(p_belongs[idx])
        datatype = get_datatype_by_str(p_type[idx])
        parameters[pname.lower().strip()] = Parameter(pname, datatype, belongs)
    return parameters

parameters = read_hadoop_params()

def get_belong_by_pname(name):
    name = name.strip().lower()
    p = parameters.get(name.strip())
    if p is None:
        return None
    conf_file = p.get_conf_file()
    return conf_file


def write_into_conf_file(pv_dict, folder):
    '''
        Write out parameter-value dictionary into a configuration XML file
    '''
    conf_files = []  # a list of configuration files
    make_folder_ready(folder)
    separate_confs = {}
    for p, v in pv_dict.items():
        belong_name = get_belong_by_pname(p.lower())
        if belong_name == None:
            continue
        if belong_name in separate_confs:
            separate_confs[belong_name].append((p, v))
        else:
            separate_confs[belong_name] = [(p, v)]

    for file_name, pvs in separate_confs.items():
        content = create_xml_str(pvs)
        file_path = folder + os.sep + file_name
        with open(file_path, 'w') as fp:
            fp.write(content)
        conf_files.append(file_name)
    return conf_files


def create_xml_str(pv_dict):
    root = ET.Element("configuration")
    for p, v in pv_dict:
        doc = ET.SubElement(root, "property")
        ET.SubElement(doc, "name").text = str(p).strip()
        ET.SubElement(doc, "value").text = str(v).strip()
        # ET.SubElement(doc, "final").text = 'true'
    # tree = ET.ElementTree(root)
    xmlstr = minidom.parseString(ET.tostring(root)).toprettyxml(indent="   ")
    return xmlstr


def get_latest_performance():
    profile_res_file = cfg.hibench_home + '/report/wordcount/hadoop/bench.log'
    with open(profile_res_file, 'r') as fp:
        lines = fp.readlines()
        for i in range(len(lines)-1, 0, -1):
            line = lines[i].strip()
            if line.startswith('CPU time'):
                perf = int(line.split('=')[-1])
                return perf
