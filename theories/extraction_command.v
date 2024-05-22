From trajectories Require Import generic_trajectories smooth_trajectories.
Require Import QArith.

Extraction "smooth_trajectories" smooth_point_to_point example_bottom example_top
  example_edge_sets example_point_spread_sets Qred.
