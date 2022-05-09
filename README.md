# copland-avm
Copland Attestation Virtual Machine definition and tools

## Quick Browsing

Using any browser, open the html files in `src/html` to browse all definitions and theorem statements pretty-printed.  All definitions are click-navigable.

## Build Instructions

To compile all the proof script dependencies in `src/` and step through them interactively, make sure you have [Coq](https://coq.inria.fr/opam-using.html) and [ProofGeneral](https://proofgeneral.github.io/) installed on your system (Tested on Coq versions 8.11 and 8.12), then type:

`cd src ; make`

Once compilation completes, open the desired `.v` file in `src/` to step through its definitions and proofs (`make` will also re-generate the pretty-printed html in `src/html` for quick browsing).

## Source File Descriptions

### Preamble.v through Main.v are mostly copies of the original Coq source files from the "Orchestrating Layered Attestations" paper [(link)](https://ku-sldg.github.io/copland///resources/copland-post-2019.pdf), with minor modifications for automation and updates to the Copland language.  Those original specs/proofs can be found [here](https://ku-sldg.github.io/copland/software.html).
---
* Preamble.v:  Helper tactics used throughout the proofs.
* More_lists.v:  Facts about lists
* StructTactics.v:  Local copy of structural tactics library from:  https://github.com/uwplse/StructTact
* Defs.v:  General (non-Copland-specific) automation tactics
* BS.v:  Abstract definition of the raw binary string (`BS`) datatype.
* Term_Defs.v:  Definitions of main Copland syntactic structures:  phrases(`Term`), Evidence (`Evidence`), events (`Ev`), raw evidence(`RawEv`), type-tagged evidence (`EvC`), evidence semantics (`eval`), annotated phrases (`AnnoTerm`), parallel annotated terms (`AnnoTermPar`), and lemmas about annotation and term well-formedness.
* Eqb_Evidence.v:  Decidable equality lemmas for Copland terms and evidence.
* Term.v:  `events` relation mapping phrases and evidence to the attestation-relevant events they generate, various lemmas about events and well-formed phrases.
* Event_system.v:  Abstract event systems (event orderings)
* Term_system.v:  Copland-specific event systems (denotational reference semantics)
* Trace.v:  Event traces and their relation to event systems
* LTS.v:  Small-step, labelled transition system reference semantics for Copland
* Main.v:  Main theorems for Copland reference semantics
* ConcreteEvidence.v:  Evidence structure that models concrete results of Copland phrase execution (`EvidenceC`), `Evidence` and `EvidenceC` sub-term relations (`EvSubT` and `EvSub`).
* StMonad_Coq.v:  General definition of a state monad with error + monadic notations, borrowed/tweaked from:  https://github.com/uwplse/verdi/blob/master/core/StateMachineHandlerMonad.v
* OptMonad_Coq.v:  General option monad + notations
* Cvm_St.v:  Record representing the CVM Monad state structure(`cvm_st`) + CVM monad definition (`CVM`).
* IO_Type.v:  IO type, defined as alias to CVM monad.  Useful as its own module for extraction.
* IO_Stubs.v:  Abstract (Admitted) definitions of IO function signatures (measurements, crypto, communication) that must be filled in for a concrete execution.
* Axioms_Io.v:  Uninterpreted functions and rewrite rules that model external (remote and local parallel) components that interpret Copland phrases
* Evidence_Bundlers.v:  Helper functions that simultaneously bundle raw evidence and update a related evidence type structure.  Used by the CVM to update the internal type-tagged evidence structure (`EvC`).  
* Cvm_Monad.v:  CVM Monad monadic helper functions (workhorses of the CVM implementation).
* Cvm_Impl.v:  Top-level monadic function implementing the Copland Compiler/VM (`copland_compile`).
* Cvm_Run.v:  CVM monad run functions.
* Auto.v:  More automation tactics.  Mostly generic, some cvm-monad-specific.
* Helpers_VmSemantics.v:  Helper lemmas for proofs about the CVM semantics.
* AutoApp.v:  More automation.
* External_Facts.v:  Axioms and lemmas that capture the semantics of external CVM instances.
* Appraisal_Evidence.v:  Functions and lemmas that relate raw and structured evidence, useful for both CVM execution and appraisal.  Also some wrappers/automation for `copland_compile` and annotated terms.
* CvmSemantics.v:  Main proofs about the Copland Virtual Machine implementation, linking it to the Copland reference semantics. 
* Appraisal_IO_Stubs.v:  Abstract (Admitted) definitions of IO function signatures for primitive appraisal checkers.
* Appraisal_Defs.v:  Helper functions for appraisal procedure +
  predicates used for stating appraisal correctness + predicates
  restricting well-formed phrases and evidence that are appraisable.
* Impl_appraisal.v:  Top-level function implementing appraisal, simultaneous walk over raw evidence and evidence type.  Defined in the option monad for now (lifts to AM monad in extracted code).
* Impl_appraisal_alt.v:  Top-level function implementing appraisal over `EvidenceC` representation (non-monadic primitive checkers for now).
* Test_Extract_App.v:  Experimental code extraction module.
* Appraisal_AltImpls_Eq.v:  Proof that alternative appraisal implementations are equivalent modulo evidence representations.
* Helpers_Appraisal.v:  Helper lemmas for proofs about appraisal correctness.
* Appraisal.v:  Main proofs for appraisal correctness.



<!--
* EqClass.v:  Generic Typeclass for equality, plus some instances

* Maps.v:  Polymorphic, list-based implementation of finite maps, borrowed/tweaked from: https://softwarefoundations.cis.upenn.edu/qc-current/TImp.html

* MonadLaws.v:  Proofs of monad laws for the general state monad in GenStMonad.v

* MonadVMFacts.v:  Lemmas and LTAC scripts to leverage facts about the CVM Monad

* StAM.v:  Record representing the AM Monad state structure
* MonadAM.v:  Definition of the AM Monad + monadic helper functions
-->

<!-- ### Copland Compiler and VM specs/proofs -->

## Questions?
Contact author/maintainer (Adam Petz) at: ampetz@ku.edu
