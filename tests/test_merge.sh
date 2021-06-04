#!/bin/bash

../bin/randaut 10 -Q 10000..11000 > aut.hoa
./run merge_states_time.py
../bin/randaut 2 -Q 10000..11000 > aut.hoa
./run merge_states_time.py
