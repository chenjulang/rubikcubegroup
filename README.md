# rubiks-cube

## The Project, In Brief
This is a project for CS 1951x: Formal Proof and Verification. It is focused on representing the Rubik's Cube and proving various facts about it and the mathematical group of possible cube states, as well as formalizing an algorithm for solving the cube.

## Representing the Cube
Much of this code is inspired by [kendfrey's rubiks-cube-group repository](https://github.com/kendfrey/rubiks-cube-group). Specifically, I modeled the Rubik's Cube using the same division of information into corner pieces and edge pieces and then with respect to permutations and orientations of these sets of pieces. I also copied the code for the widget to display states of the cube and adapted it to Lean 4, making it compatible with the representation(s) used here.

I experimented with two approaches to representing the orientations of the pieces: vectors and functions. I initially only used vectors, but found that functions made some proofs easier to complete. Nevertheless, I have kept two separate files for the vector-based and function-based definitions as well as their corresponding proof files. The `SolutionAlgorithm.lean` file uses the function-based representation. The function-based files contain comments explaining some of their structure, and vector-based files mirror the structure of their function-based counterparts.

## Solving the Cube
The approach used in the solution algorithm is based on the Old Pochmann method, which is explained in [this video](https://youtu.be/ZZ41gWvltT8?si=H5LTXiRIMsc2TSEk) and on [this website](https://www.speedcubereview.com/blind-solving-algorithms.html). Specifically, I implement a version that only uses intuitive setup moves in combination with the T Perm for edges and the Altered Y Perm for corners. Note that since edges are solved first, the edge setup moves are allowed to disturb the UBR and URF corners, since these pieces aren't being memorized. The corner setup moves, however, are designed to not disturb the UB and UL edges, which swap every time the Altered Y Perm algorithm is applied.