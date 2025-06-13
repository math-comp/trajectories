# Trajectories

This archive contains the formal development described in submission
 "Formally verifying a vertical cell decomposition algorithm".  This branch
contains the snapshot at the time of publication.  To see a more up to date
version of the development, you should rather use branch main, where
improvements made later than the paper publication are included.

## Building and installation instructions

The easiest way to compile this software is to rely on opam.  First install
opam on your machine using the adapted command for your architecture.  Then
perform the following actions, which assume you created a switch (we tested
the procedure with a switch using `ocaml.4.14.1`).

To build and install manually, do:

```shell
git clone git@github.com:math-comp/trajectories -b vertical-cell-papers
cd trajectories
opam repo add coq-released https://coq.inria.fr/opam/released
opam install -y --deps-only ./trajectories.opam
make
cd www
make
```
In our experience, executing the line `opam install ...` can take around 10
minutes.  Executing the line `make` in directory `trajectories` can take around
3 minutes.
Executing the line `make` in directory `www` can take around 5 seconds.

The main lemmas from the paper `second_phase_safety` and `two_phase_safety`
are proved in file `theories/step_correct.v`.

The following bash command line makes it possible to check the statement
of `two_phase_safety` and to verify that it does not rely on unwanted
assumptions.

```
echo "Check two_phase_safety.  Print Assumptions two_phase_safety." | \
coqtop -R theories trajectories -require-import step_correct \
 -require-import generic_trajectories -require-import points_and_edges \
 -require-import-from mathcomp all_ssreflect \
 -require-import-from mathcomp all_algebra -require-import cells
```

## To run the interactive demonstration

while in directory `www`

```shell
make run
```
Then open the address `http://0.0.0.0:8000/grid.html` in a web-browser on the
same machine.  The vertical cells that are created by the algorithms in
the paper are visible when one checks the box "Show cells".


These instructions have been tested on a linux machine.
