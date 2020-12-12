# copland-avm
Copland Attestation Virtual Machine definition and tools

## Quick Browsing

Using any browser, open the html files in `src/html` to browse all definitions and theorem statements pretty-printed.  All definitions are click-navigable.

## Build Instructions

Make sure you have [Coq](https://coq.inria.fr/opam-using.html) and [ProofGeneral](https://proofgeneral.github.io/) installed on your system (Tested on Coq version 8.12.0), then type:

`cd src ; make`

You can now walk through the proof scripts in `src/` interactively.  This will also re-generate the pretty-printed html in `src/html`.

## Source File Descriptions

### Original Coq source files from the "Orchestrating Layered Attestations" paper [(link)](https://ku-sldg.github.io/copland///resources/copland-post-2019.pdf), slightly modified (see modification notes [below](#Modifications-to-Original-Copland-spec/proofs)).  See full original specs/proofs [here](https://ku-sldg.github.io/copland/software.html).
---
* Preamble.v:  Helper tactics used throughout the proofs.
* More_lists.v:  Facts about lists
* Term.v:  Copland terms, events, and annotated terms
* Event_system.v:  Abstract event systems
* Term_system.v:  Copland-specific event systems
* Trace.v:  Traces and their relation to event systems
* LTS.v:  Small-step, labelled transition system reference semantics for Copland
* Main.v:  Main theorems for Copland reference semantics


### Copland Compiler and VM specs/proofs
---
* StructTactics.v:  Local copy of structural tactics library from:  https://github.com/uwplse/StructTact
* ConcreteEvidence.v:  Evidence structure that models concrete results of Copland phrase execution.  
* Maps.v:  Simple, list-based implementation of finite maps
* StVM.v:  Record representing the AVM Monad state structure
* GenStMonad.v:  General definition of a state monad with error + monadic notations
* MonadVM.v:  Definition of the AVM Monad + monadic helper functions
* MonadVMFacts.v:  Lemmas and LTAC scripts to leverage facts about the AVM Monad
* VmSemantics.v:  Implementation of the Attestation Virtual Machine (AVM) + proof that it refines the Copland reference semantics
* MonadLaws.v:  Proofs of monad laws for the general state monad in GenStMonad.v
* Maps_Class.v:  
* EqbPair.v 
* Axioms_Io.v
* Impl_vm.v
* Helpers_VmSemantics.v
* External_Facts.v
* Auto.v

## Modifications to Original Copland spec/proofs
1. 
