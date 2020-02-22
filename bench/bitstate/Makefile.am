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

AM_CPPFLAGS = -I$(top_builddir) -I$(top_srcdir) $(BUDDY_CPPFLAGS) \
              -I$(top_builddir)/lib -I$(top_srcdir)/lib
AM_CXXFLAGS = $(CXXFLAGS)

LDADD =						\
  $(top_builddir)/bin/libcommon.a		\
  $(top_builddir)/lib/libgnu.la			\
  $(top_builddir)/spot/libspot.la		\
  $(top_builddir)/buddy/src/libbddx.la		\
  $(top_builddir)/spot/ltsmin/libspotltsmin.la

bin_PROGRAMS = bitstate

bitstate_SOURCES = bitstate.cc

CLEANFILES = *.dve *.dve2C *.dve.cpp
