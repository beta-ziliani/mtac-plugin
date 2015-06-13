# Mtac as a Plugin
Typed Tactics for Coq 8.5

Copyright (c) 2015 Beta Ziliani <bziliani@famaf.unc.edu.ar>

Based on Mtac 1.2, with contributions from Jan-Oliver <janno@mpi-sws.org>.

Distributed under the terms of the MIT License, see LICENSE for details.

This archive contains the intepreter of Mtac as a plugin.

The archive has 3 subdirectories:

    src contains the code of the plugin in mtac.ml4, and the interpreter in run.ml.

    theories contains support Coq files for the plugin. Mtac.v
    declares the plugin on the Coq side, and the main inductive type
    for Mtac. Hash.v is a hash-table, and Mtactics.v contains some useful tactics.

    test-suite contains files testing the different features of Mtac.

Installation
============

The plugin works currently with Coq v8.5. Through OPAM, 
this plugin is available in Coq's repo-unstable:
```
 # opam install coq:mtac
```
Otherwise, you should have coqc, ocamlc and make in your path. 
Then simply do:
```
 # ./configure.sh
```
To generate a makefile from the description in Make, then `make`.
This will consecutively build the plugin, the supporting 
theories and the test-suite file.

You can then either `make install` the plugin or leave it in its
current directory. To be able to import it from anywhere in Coq,
simply add the following to `~/.coqrc`:
```
Add LoadPath "path_to_mtac/theories" as Unicoq.
Add ML Path "path_to_mtac/src".
```
# Usage

Once installed, you can `Require Import Mtac.Mtac` to load the
plugin. The plugin defines the following option to execute a
Mtactic:
- Tactic `run t as h` taking Mtactic t and defining h as the
  result of the execution of the tactic in the local environment.
- Tactic `rrun t` taking Mtactic t and refining the current goal 
  with the result of the execution of the tactic.
- Notation `Mrun t` to execute Mtactic t as part of a term.
