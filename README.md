# Trajectories

This archive contains the formal development described in submission
 "Formally verifying a vertical cell decomposition algorithm"

## Building and installation instructions

The easiest way to compile this software is to rely on opam.  First install
opam on your machine using the adapted command for your architecture.  Then
perform the following actions, which assume you created a switch (we tested
the procedure with a switch using `ocaml.4.14.1`).

To instead build and install manually, do:

```shell
tar xfz trajectories.tgz
cd trajectories
opam install --deps-only trajectories.opam
make
cd www
make
```
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


These instruction have been tested on a linux machine.