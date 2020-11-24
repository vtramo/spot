#!/usr/bin/env python3
## -*- coding: utf-8 -*-
## Copyright (C) 2020 Laboratoire de Recherche et Développement de
## l'Epita (LRDE).
##
## This file is part of Spot, a model checking library.
##
## Spot is free software; you can redistribute it and/or modify it
## under the terms of the GNU General Public License as published by
## the Free Software Foundation; either version 3 of the License, or
## (at your option) any later version.
##
## Spot is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
## or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
## License for more details.
##
## You should have received a copy of the GNU General Public License
## along with this program.  If not, see <http://www.gnu.org/licenses/>.

import csv
import numpy as np
import os
import sys
from matplotlib import pyplot as plt

from correlations import *
from gui import *
from plot import *

def get_simple_features(features, names):
    res = []
    for name in names:
        if np.unique(features[name]).size <= 3:
            res.append(name)
    return res

def read_csv(filename, blacklist=['time', 'model', 'formula']):
    threads = []
    with open(filename, newline='') as csvfile:
        reader = csv.DictReader(csvfile)
        features = {}
        simplenames = []
        # read header
        for name in reader.fieldnames:
            if name not in blacklist:
                features[name] = np.empty((0))
                if 'bloemen' in name:
                    split = name.split('_')
                    if len(split) == 2:
                        threads.append('')
                    else:
                        threads.append('_' + split[-1])
        # read body
        for row in reader:
            for feature in features:
                try:
                    features[feature] = np.append(features[feature],
                                                  float(row[feature]))
                except ValueError:
                    features[feature] = np.append(features[feature],
                                                  row[feature])
                    if feature not in simplenames:
                        simplenames.append(feature)
    names = []
    for f in features:
        names.append(f)
    for name in get_simple_features(features, names):
        if name not in simplenames:
            simplenames.append(name)

    speed = features['bloemen_time' + threads[0]] /\
            features['cndfs_time' + threads[0]]
    speed = np.where(speed < 1, -1/speed + 1, speed - 1)
    features['time_difference'] = speed
    names.append('time_difference')

    return features, names, simplenames, threads

if __name__ == '__main__':
    if len(sys.argv) != 2:
        sys.exit(1)
    features, names, simplenames, threads = read_csv(sys.argv[1])

    cachefolder = '.cache_' + os.path.basename(sys.argv[1]) + '/'
    if not os.path.exists(cachefolder):
        os.mkdir(cachefolder)
    if not os.path.exists(cachefolder + '/scps'):
        os.mkdir(cachefolder + '/scps')

    generate_time_scatter_plot(features, names, cachefolder, threads)
    gui_display(features, names, simplenames, cachefolder, threads)
