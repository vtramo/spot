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

import numpy as np
import os
import copy
from matplotlib import pyplot as plt

def filter_features(features, names, excluded, filter, value):
    f = copy.deepcopy(features)
    excludedvalues = features[filter]
    for e in excluded:
        f.pop(e)
    mask = (excludedvalues == value)
    for feature in f:
        f[feature] = f[feature][mask]
    return f

def scatter_plot(x, y, title='', xlabel='', ylabel='', axes=False):
    plt.title(title)
    plt.xlabel(xlabel)
    plt.ylabel(ylabel)

    if axes:
        min_ = min(np.amin(x), np.amin(y))
        max_ = max(np.amax(x), np.amax(y))
        plt.plot([min_, max_], [min_, max_], '-k', label='x = y axis')
    plt.plot(x, y, 'ob')
    if axes:
        alpha = (np.sum(x * y) - np.sum(x) * np.sum(y) / x.size)\
                / (np.sum(x * x) - ((np.sum(x) ** 2) / x.size))
        plt.plot([min_, min(max_, max_ / alpha)],
                 [min_, min(max_, alpha * max_)], 'k-', linestyle='--',
                 label='linear regression')
        plt.legend()

def basic_plot(x, y, title='', xlabel='', ylabel=''):
    plt.plot(y, x, 'ob')
    plt.title(title)
    plt.xlabel(xlabel)
    plt.ylabel(ylabel)

def generate_time_scatter_plot(features, names, foldername, threads, extraname=''):
    for thr in threads:
        filename = foldername + 'time_difference%s.png' % (extraname + thr)
        if os.path.isfile(filename):
            return
        bloemen_time = features['bloemen_time' + thr]
        cndfs_time = features['cndfs_time' + thr]
        extraname = ' ' + extraname if extraname else extraname
        scatter_plot(bloemen_time, cndfs_time, 'time difference' + extraname + thr,
                     'bloemen time', 'cndfs time', True)
        plt.savefig(filename)
        plt.clf()
