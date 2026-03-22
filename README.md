# Lean 4 Project Template

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Zulip : Topic](https://img.shields.io/badge/Zulip-Topic-%237E57C2.svg?logo=zulip&logoColor=white)](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Tutorial.3A.20Getting.20Started.20with.20Blueprint-Driven.20Projects)
[![YouTube : Tutorial](https://img.shields.io/badge/YouTube-Tutorial-%23FF0000.svg?logo=youtube&logoColor=white)](https://youtu.be/KyuyTsLgkMY)


This repository is  blueprint-driven formalization project for SMSG-based elementary geometry in Lean 4.

## Create a Project Folder

Create a project folder on your local machine. Make sure that you know how to open a shell (in Windows that's the "Windows Terminal") and how to find your project folder.

## Install Lean 4 (optional until you program in Lean)

Ensure that you have a functioning Lean 4 installation. If you do not, please follow
the [Lean installation guide](https://leanprover-community.github.io/get_started.html).

## Preliminaries to use this Repository

Make sure that the following prerequisits are fulfilled:

1. VS Code installed
2. git installed connected to [git.UP](https://gitup.uni-potsdam.de) via ssh (best version)
3. python and pip3 installed
4. a full latex distribution including latexmk, xetex and pdflatex installed


## Clone this Repository

Open a shell an go to your project folder.

Clone this repository into your project folder (using ssh):

```bash
git@gitup.uni-potsdam.de:lean_4_projekte/smsg_axiome/anna_ledwon.git
```

This will create a sub-folder `anna_ledwon` in your project folder which contains all the necessary files.

## Install Leanblueprint

[Leanblueprint](https://github.com/PatrickMassot/leanblueprint) is a GitHub focused tool to facilitate managing lean projects by

1. providing relatively automated documentation
2. allowing to write a graphical representation of the logical structure of the mathematics, i.e. a dependency graph
3. providing a light weight web server to display everything

Some of the features of leanblueprint will not work here since this project is based on GitLab (git.UP) and not GitHub. But the main features will function.

In particular leanblueprint will not "run" on git.UP. This is in contrast to GitHub where leanblueprint is exectuted and provides a publically available web page. This feature is not available on git.UP.

The Repository has already been fully configured, so there is no need to use leanblueprint for this (and this will not work out of the box).

To install leanblueprint execute

```bash
pip install leanblueprint
```

in your shell.

Now you are basically done and can start working with the 

## Repository Layout

The most important folders in your git folder `anna_ledwon` are the folders
1. `anna_ledwon` (sorry, I used the name twice while setting everything up) where the lean-code is stored.
2. `blueprint/src` where you can find the file `content.tex`. This is the main tex-file for blueprint where the documentation is written.
3. `blueprint/print` where you can find the file `print.pdf` which contains the latex output of `content.tex`.

## Using Blueprint

I have built a simple example in `context.tex`. I hope this is a good starting point. You can write as if you would write a normal latex file. 

**Important** The file `context.tex` must start with a `\chapter{}`.

To work with leanblueprint proceed as follows:

1. write your latex code in `context.tex` and save your code
2. run the following code in your shell:
   ```bash
   leanblueprint web
   ```
   This will generate the blueprint graph and the html code to display the graph and your latex code.
3. run 
    ```bash 
    leanblueprint serve
    ```
    and open the web page [http://0.0.0.0:8000/](http://0.0.0.0:8000/) in your browser. 
4. to get your latex code as a pdf run
   ```bash
   leanblueprint pdf
   ```
   Then open the `print.pdf` file. 


## Selected Projects Using this Template

You can find more elaborate examples for dependency graphs in these public projects:

- [Infinity Cosmos](https://github.com/emilyriehl/infinity-cosmos) by Emily Riehl et al.
- [Analytic Number Theory Exponent Database](https://github.com/teorth/expdb) by Terence Tao et al.
- [Equational Theories](https://github.com/teorth/equational_theories) by Terence Tao et al.
- [Groupoid Model of Homotopy Type Theory](https://github.com/sinhp/GroupoidModelofHoTTinLean4) by Sina Hazratpour et al.
- [Soundness of FRI](https://github.com/BoltonBailey/FRISoundness) by Bolton Bailey et al.
- [Weil's Converse Theorem](https://github.com/CBirkbeck/WeilConverse) by Chris Birkbeck et al.
- [Proofs from THE BOOK](https://github.com/mo271/FormalBook) by Moritz Firsching et al.
- [Automata Theory](https://github.com/shetzl/autth) by Stefan Hetzl et al.
- [Dirichlet Nonvanishing](https://github.com/CBirkbeck/DirichletNonvanishing) by Chris Birkbeck et al.
- [Seymour's Decomposition Theorem](https://github.com/Ivan-Sergeyev/seymour) by Ivan Sergeyev et al.
- [Spectral Theorem](https://github.com/oliver-butterley/SpectralThm) by Oliver Butterley and Yoh Tanimoto.
- [NeuralNetworks](https://github.com/or4nge19/NeuralNetworks) by Matteo Cipollina.
- [ABC Exceptions](https://github.com/b-mehta/ABC-Exceptions) by Bhavik Mehta et al.
- [Sphere Packing in 8 Dimensions](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean) by Maryna Viazovska et al.
