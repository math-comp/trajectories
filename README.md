# Trajectories

This archive contains the formal development described in submission
 "Formally verifying a vertical cell decomposition algorithm"

## Building and installation instructions

The easiest way to compile this software is to rely on opam.  First install
opam on your machine using the adapted command for your architecture.  Then
perform the following actions, which assume you created a switch (we tested
the procedure with a switch using `ocaml.4.14.1`).

To build and install manually, do:

```shell
tar xfz trajectories.tgz
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

## To run the interactive demonstration

while in directory `www`

```shell
make run
```
Then open the address `http://0.0.0.0:8000/grid.html` in a web-browser on the
same machine.  The vertical cells that are created by the algorithms in
the paper are visible when one checks the box "Show cells".


These instructions have been tested on a linux machine.
