# copland-avm
Copland Attestation Virtual Machine definition and tools

## Build Instructions

Make sure you have [Coq](https://coq.inria.fr/opam-using.html) installed on your system (Tested on version 8.12.0), then type:

`cd src ; make`

You should now be able to walk through the proof scripts in the `src/` directory interactively (Tested with [ProofGeneral](https://proofgeneral.github.io/), not CoqIDE).

Alternatively, browse the pretty-printed html generated in `src/html`.

## Source File Descriptions

### Original Coq specs/proofs from the ["Orchestrating Layered Attestations" paper](https://ku-sldg.github.io/copland///resources/copland-post-2019.pdf), slightly modified (see modification notes [below](#Modifications-to-Original-Copland-spec/proofs)).  See full original specs/proofs [here](https://ku-sldg.github.io/copland/software.html).
---
* Preamble.v:  Helper tactics used throughout the proofs.
* More_lists.v:  Facts about lists
* Term.v:  Copland terms, events, and annotated terms
* Event_system.v:  Abstract event systems
* Term_system.v:  Copland-specific event systems
* Trace.v:  Traces and their relation to event systems
* LTS.v:  Small-step, labelled transition system reference semantics for Copland
* Main.v:  Main theorems for Copland reference semantics


### Additional Coq specs/proofs
---
* StructTactics.v:  Local copy of structural tactics library from:  https://github.com/uwplse/StructTact
* ConcreteEvidence.v:  Evidence structure that models concrete results of Copland phrase execution.  
* Maps.v:  Simple, list-based implementation of finite maps
* StVM.v:  Record representing the AVM Monad state structure
* StAM.v:  Record representing the AM Monad state structure
* Instr.v:  AVM instruction set and Copland Compiler implementation
* MyStack.v:  Simple, list-based stack implementation
* GenStMonad.v:  General definition of a state monad with error + monadic notations
* MonadVM.v:  Definition of the AVM Monad + monadic helper functions
* MonadVMFacts.v:  Lemmas and LTAC scripts to leverage facts about the AVM Monad
* VmSemantics.v:  Implementation of the Attestation Virtual Machine (AVM) + proof that it refines the Copland reference semantics
* MonadLaws.v:  Proofs of monad laws for the general state monad in GenStMonad.v
* RunAlt.v:  Alternative ("big-step") definition of run\_vm + proof that it corresponds to the one in VmSemantics.v

## Modifications to Original Copland spec/proofs
1. 
