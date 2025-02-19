<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Trajectories

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/math-comp/trajectories/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/math-comp/trajectories/actions?query=workflow:"Docker%20CI"




TODO

## Meta

- Author(s):
  - Reynald Affeldt (initial)
  - Yves Bertot (initial)
- License: [CeCILL-C](LICENSE)
- Compatible Coq versions: Coq >= 8.19, MathComp >= 2.2.0
- Additional dependencies:
  - [MathComp ssreflect 2.2.0 or later](https://math-comp.github.io)
  - [MathComp fingroup 2.2.0 or later](https://math-comp.github.io)
  - [MathComp algebra 2.2.0 or later](https://math-comp.github.io)
  - [MathComp solvable 2.2.0 or later](https://math-comp.github.io)
  - [MathComp field 2.2.0 or later](https://math-comp.github.io)
  - [Mathcomp real closed 2.0.0 or later](https://github.com/math-comp/real-closed/)
  - [Algebra tactics 1.2.0 or later](https://github.com/math-comp/algebra-tactics)
  - [MathComp analysis 1.0.0 or later](https://github.com/math-comp/analysis)
  - [Infotheo 0.7.0 of later](https://github.com/affeldt-aist/infotheo)
- Coq namespace: `mathcomp.trajectories`
- Related publication(s):
  - [Safe Smooth Paths between Straight Line Obstacles](https://inria.hal.science/hal-04312815) doi:[https://doi.org/10.1007/978-3-031-61716-4_3](https://doi.org/https://doi.org/10.1007/978-3-031-61716-4_3)

## Building and installation instructions

The easiest way to install the latest released version of Trajectories
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-trajectories
```

To instead build and install manually, do:

``` shell
git clone https://github.com/math-comp/trajectories.git
cd trajectories
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


This directory contain a variety of developments that were  thought to be
useful for the computation of trajectories between obstacles.

The leading example relies on a decomposition of a plane area in vertical
cells, which gives a graph whose nodes are the cells.  The next step is to
compute a path in this graph, from which a piecewise straight line
trajectory is computed, which is guaranted to stay inside the safe cells, or
to go from one cell to a neighbor only through a safe crossing.  The final
step is to smoothen the trajectory, by using Bezier curves for which checks
are performed to verify that they stay within the safe part of the area.

A demonstration version is available at [this page](https://stamp.gitlabpages.inria.fr/trajectories.html).

## Disclaimer

TODO

## Documentation

tentative update of https://gitlab.inria.fr/bertot/cadcoq

references:
- Root Isolation for one-variable polynomials (2010)
  https://wiki.portal.chalmers.se/cse/uploads/ForMath/rootisol
- A formal study of Bernstein coefficients and polynomials (2010)
  https://hal.inria.fr/inria-00503017v2/document
- Theorem of three circles in Coq (2013)
  https://arxiv.org/abs/1306.0783
- Safe Smooth Paths between straight line obstacles
  https://inria.hal.science/hal-04312815
  https://link.springer.com/chapter/10.1007/978-3-031-61716-4_3

## Development information

On April 2, 2023, a file `smooth_trajectories.v` was added to illustrate a
program to compute smooth trajectories for a "point" between obstacles given
by straight edges.

The example can be played with by changing the contents of variables 
`example_bottom`, `example_top`, `example_edge_list`, and changing
the coordinates of points given as argument to `example_test` in the
`Compute` command that appears at the end of the file.  This compute
 commands produces text that should be placed in a postscript file and
 can be displayed with any postscript enabled viewer.  A perl-script is
 provided to produce this, so that the following command is a handy
 way to produce example outputs:

 ```
 (cd theories; ./run_tests.sh)
 ```

At the time of writing this paragraph, the code seems complete but
many bugs have been found in parts of the code that have not been proved
formally.

If you play with this code and you obtain a trajectory that obviously
crosses the given edges, please report.

## Previous work reused at the time of the first releases

TODO

## Acknowledgments

TODO
