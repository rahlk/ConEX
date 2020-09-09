# ConEX: Efficient Exploration of Big-Data System Configurations for Better Performance

![](./logo.jpg)

## Submission 

Published in IEEE Transactions on Software Engineering (TSE) 2020. ARXIV Link: [https://arxiv.org/abs/1910.09644](https://arxiv.org/abs/1910.09644]

## Cite as:
```
@article{krishna2020conex,
  title={ConEx: Efficient Exploration of Big-Data System Configurations for Better Performance},
  author={Krishna, Rahul and Tang, Chong and Sullivan, Kevin and Ray, Baishakhi},
  journal={IEEE Transactions on Software Engineering},
  year={2020},
  publisher={IEEE}
}
```


## Abstract

Configuration space complexity makes the big-data software systems hard to configure well. Consider Hadoop, with over
nine hundred parameters, developers often just use the default configurations provided with Hadoop distributions. The opportunity
costs in lost performance are significant. Popular learning-based approaches to auto-tune software does not scale well for big-data
systems because of the high cost of collecting training data. We present a new method based on a combination of Evolutionary Markov
Chain Monte Carlo (EMCMC) sampling and cost reduction techniques to find better-performing configurations for big data systems. For
cost reduction, we developed and experimentally tested and validated two approaches: using scaled-up big data jobs as proxies for the
objective function for larger jobs and using a dynamic job similarity measure to infer that results obtained for one kind of big data
problem will work well for similar problems. Our experimental results suggest that our approach promises to improve the performance
of big data systems significantly and that it outperforms competing approaches based on random sampling, basic genetic algorithms
(GA), and predictive model learning. Our experimental results support the conclusion that our approach strongly demonstrates the
potential to improve the performance of big data systems significantly and frugally.


## Overview
![image](https://user-images.githubusercontent.com/1433964/92539328-222c9600-f20f-11ea-8782-03a1d82cc7f7.png)


## Authors
+ Rahul Krishna†(a), Chong Tang†(b), Kevin Sullivan, and Baishakhi Ray
  - † Rahul Krishna and Chong Tang are _joint first authors_
  - Tang, C. is with Walmart Labs, Mountain View, CA USA. E-mail: ct4ew@virginia.edu
  - Sullivan, K. is with the Department of Computer Science, University of Virginia, Charlottesville, VA USA. E-mail: sullivan@virginia.edu
  - Ray, B. and Krishna, R. are with the Department of Computer Science, Columbia University, New York City, NY USA. E-mail: rayb@cs.columbia.edu and i.m.ralk@gmail.com
