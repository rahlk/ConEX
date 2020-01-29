
imp_params_file = 'important_params_ranked.csv'
imp_params = []
with open(imp_params_file, 'r') as fp:
    lines = fp.readlines()
    lines = [line.strip() for line in lines]
    imp_params = lines

import pandas as pd
all_param_values = pd.read_excel('params_values.xlsx', header=0)
indes_to_drop = []
for index, row in all_param_values.iterrows():
    if row['Parameters'] not in imp_params:
        indes_to_drop.append(index)

new_df = all_param_values.drop(indes_to_drop)

write_to_file = pd.ExcelWriter('important_params_valus.xlsx')
new_df.to_excel(write_to_file)
write_to_file.save()
