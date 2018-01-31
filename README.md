# Automated Proof Verification with Coq 
## Verifying properties of 2-by-2 matrices and a simple OCaml based lanuage

## About
This repository contains 2 coq files, and 2 corresponding write-ups. The coq files contain proofs of properties of 2-by-2 matrices (defined conveniently by Ocaml's variant features), and properties of a simple Ocaml based language (including properties of its compilers, interpreters, and virtual machine). This repository is the result of Yale-NUS College's Function Programminga and Proving course (YSC3236) run in the fall of AY2017-18 by Professor Olivier Danvy. 

## Background
Automated proof verification has been around since the 1970s, and refers to the process of using computers (as opposed to human intuition) to prove both properties of programs and mathematical theorems (e.g. the famous 4-colouring theorem proved by Kenneth Appel). However, it has only recently gained popularity owing to advances in the field which have greatly shortened the otherwise tedious and cumbersome process of (i) formalising programatically the syntax and semantics of programs and mathematical theories, and (ii) proving properties about these formalisations.

There exist several systems of logic to formalize programming languages. Calculus of Constructions (the name 'coq' is inspired by the acronym of which), for instance, formalizes functional languages like OCaml, Scala, Haskell,etc. Hoare logic is used to formalize imperative languages like C and C++, and most recently, work on separation logic has enabled computer scientists to prove properties of programming languages pertaining to concurrency. 

YSC3236 served as a very gentle introduction to the formidable world of automated proof verification. Using coq, which is a domain specific language for theorem proving based on OCaml,the class explored the formalization of simple mathematical theorems (E.g. Eulclid's remainder theorem), recursive data structures (e.g. binary trees and matrices), and recursive functions, and finally, simple functional programs (which are really just functions). 

In keeping with the theme of the class, the final project had two parts, one mathematical (properties of matrices), and one software based (properties of a simple programming language).

## The projects

The coq files for projects contain properties and theorems and their proofs. A detailed explanation of the theorems and properties in each coq file is provided in the write-up corresponding to the file. 

## Running the coq files


## Author
Oishik Ganguly

## Acknowledgements
Professor Olivier Danvy ran YSC3236, and I am grateful to him for introducing us to such an exciting yet niche topic as automated proof verification. 
