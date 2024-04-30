IMPORTANT: This is the source code of a double-blind submission to CP2024. 

This is a systematic-search-implemented version of NuWLS (https://github.com/filyouzicha/NuWLS).

To compile:
./make

To run solver:
./nuwls {instance_name.wcnf} random_seed
// only .wcnf files are supported
// remember to specify the random seed

To stop:
use ^c(ctrl+c), or TIMEOUT {cutoff} command 

Output: 
A .json file will be output report the objective, time and other statistics, in the root directory of the project.
