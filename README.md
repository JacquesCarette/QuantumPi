[![DOI](https://zenodo.org/badge/595292039.svg)](https://zenodo.org/badge/latestdoi/595292039)
# QuantumPi
Code repository for our work on Quantum Pi "How to Bake a Quantum \Pi"

Tested with Agda version 2.6.4.1, stdlib-2.0 and agda-categories 0.2.0.
Things should work with 2.6.4.3 as well. Interactive versions have been
tested with Emacs 27.2 (on Linux, MacOS and WSL).

## Source install
You need to install Agda and stdlib-2.0. See 
[Agda installation](https://agda.readthedocs.io/en/latest/getting-started/installation.html) and [Library Management](https://agda.readthedocs.io/en/latest/tools/package-system.html) for the standard ways to do this. Warning: if you
have not done this before, this can be quite finicky. Please seek the help
of someone who has done it before.

For the purposes of these instructions, we will assume as unix-like system
(so any flavour of Linux, MacOS X or WSL on Windows) with command-line
instructions. Although it appears possible to do things via Visual Studio,
we have not tested this in any way.

To check everything, simply do
```
agda Everything.agda
```
at the command line. This should take less than 30 seconds, where the
bulk of the time will be spent checking `TestsSlow.agda`.

## Looking at the Code

The best entry points is `Everything.agda` which gives a quick overview
of what is all the files. The basic verification that we can indeed
correctly interpret some quantum circuits are in the modules `Tests`
and `TestsSlow`.
