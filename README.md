# Trajectories

This archive contains the formal development described in submission
 "Formally verifying a vertical cell decomposition algorithm"

## Building and installation instructions

The easiest way to compile this software is to rely on opam.  First install
opam on your machine using the adapted command for your architecture.  Then
perform the following actions, which assume you created a switch.

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-trajectories
```

To instead build and install manually, do:

```shell
tar xfz trajectories.tgz
cd trajectories
opam install --deps-only trajectories.opam
make
cd www
make
```

## To run the interactive demonstration

while in directory `www`

```shell
make run
```
Then open the address `http://0.0.0.0:8000` in a web-browser on the same
machine.

These instruction have been tested on a linux machine.