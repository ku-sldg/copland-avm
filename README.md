# copland-avm
Copland Attestation Virtual Machine definition and tools

## Quick Browsing

Using any browser, open the html files in `src/html` to browse all definitions and theorem statements pretty-printed.  All definitions are click-navigable.

## Build Instructions

To step through the proof scripts in `src/` interactively, make sure you have [Coq](https://coq.inria.fr/opam-using.html) and [ProofGeneral](https://proofgeneral.github.io/) installed on your system (Tested on Coq version 8.12.0), then type:

`cd src ; make`

Then open the desired `.v` file to step through its definitions and proofs (`make` will also re-generate the pretty-printed html in `src/html`).

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
* ConcreteEvidence.v:  Evidence structure that models concrete results of Copland phrase execution 
* Axioms_Io.v:  Uninterpreted functions and rewrite rules that model external (remote and local parallel) components that interpret Copland phrases
* EqClass.v:  Generic Typeclass for equality, plus some instances
* Maps.v:  Polymorphic, list-based implementation of finite maps
* GenStMonad.v:  General definition of a state monad with error + monadic notations, borrowed/tweaked from:  https://github.com/uwplse/verdi/blob/master/core/StateMachineHandlerMonad.v
* MonadLaws.v:  Proofs of monad laws for the general state monad in GenStMonad.v
* StVM.v:  Record representing the CVM Monad state structure
* MonadVM.v:  Definition of the CVM Monad + monadic helper functions
* MonadVMFacts.v:  Lemmas and LTAC scripts to leverage facts about the CVM Monad
* Impl_vm.v:  Implementation of the Copland Compiler and Virtual Machine
* Auto.v:  Automation scripts.  Some generic, but most specific to this development
* Helpers_VmSemantics.v:  Helper lemmas for proofs about the VM semantics
* External_Facts.v:  Axioms and lemmas that capture the semantics of external CVM instances
* VmSemantics.v:  Proofs about the Copland Virtual Machine implementation, linking it to the Copland reference semantics. 


## Modifications to Original Copland spec/proofs
1. 
